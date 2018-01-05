#lang racket

(require (for-syntax syntax/parse))

(require (except-in "../basics.rkt" go-on))
(require "../typechecker.rkt")
(require "../parser.rkt")
(require "../rep.rkt")
(require (only-in "../locations.rkt" location->syntax))
(require (except-in racket/gui yield module))
(require (prefix-in gui: racket/gui))
(require framework)
(require (prefix-in : parser-tools/lex-sre))
(require syntax-color/racket-lexer)
(require syntax/srcloc)
(require racket/generator)
(require "pie-lexer.rkt")
(require "pie-styles.rkt")
(require "print-gui.rkt")
(require data/interval-map)
(require pict)

(provide pie-slide-orientation-horizontal? pie-text%)

(current-pie-gui-font-size 40)

(define (token-sym->style s)
  (symbol->string s))


(define-syntax (go-on stx)
  (syntax-parse stx
    [(go-on () e) (syntax/loc stx e)]
    [(go-on ((p0 b0) (p b) ...) e)
     (syntax/loc stx
       (match b0
         [(go p0) (go-on ((p b) ...) e)]
         [(stop where msg) (stop where msg)]))]))

(define pie-text%
  (class (pie-styles-mixin color:text%)
    (init-field feedback pie-context)
    (init [initial-contents ""])
    (super-new)

    (define (hl-err loc)
      (when (location? loc)
        (queue-callback
         (thunk
          (define loc-stx (location->syntax loc))
          (send this clear-err)
          (send this highlight-range
                (sub1 (source-location-position loc-stx))
                (sub1 (+ (source-location-position loc-stx)
                         (source-location-span loc-stx)))
                "darkorange"
                #f
                'high
                #:key 'pie-error)))))

    (define/public (clear-err)
      (send this unhighlight-ranges/key 'pie-error))

    (define/public (type-check)
      (define txt
        (send this get-text))
      (set-box! contains-sheds? #f)
      (define contents
        (with-handlers ([exn:fail?
                         (lambda (e)
                           (send this unhighlight-ranges/key 'type-info)
                           (send this unhighlight-ranges/key 'TODO)
                           (send feedback set-error e)
                           (send feedback set-status 'bad)
                           (when (exn:srclocs? e)
                             (define wheres
                               ((exn:srclocs-accessor e) e))
                             (when (pair? wheres)
                               (hl-err (car wheres))))
                           #f)])
          (with-input-from-string txt
            (lambda ()
              (port-count-lines! (current-input-port))
              (for/list ([form (in-generator
                                (let loop ()
                                  (define form
                                    (read-syntax 'pie-editor))
                                  (unless (or (exn:fail? form)
                                              (eof-object? form))
                                    (yield form)
                                    (loop))))])
                (parse-pie-decl form))))))
      (when contents
        (queue-callback
         (thunk
          (send feedback reset)
          (send feedback set-status 'unknown)
          (send this clear-err)
          (define res (box (go (void))))
          (set-box! res
                    (let loop ([Γ pie-context]
                               [forms contents])
                      (if (null? forms)
                          (go Γ)
                          (match (car forms)
                            [`(expression ,e)
                             (go-on ((out (norm Γ e)))
                                    (begin (send feedback pprint-pie out)
                                           (loop Γ (cdr forms))))]
                            [`(claim ,name ,name-loc ,ty)
                             (hook name-loc 'definition)
                             (go-on ((new-Γ (add-claim Γ name name-loc ty)))
                                    (loop new-Γ (cdr forms)))]
                            [`(definition ,name ,name-loc ,e)
                             (hook name-loc 'definition)
                             (go-on ((new-Γ (add-def Γ name name-loc e)))
                                    (loop new-Γ (cdr forms)))]
                            [`(check-same ,loc ,type ,e1 ,e2)
                             (go-on ((_ (check-same Γ loc type e1 e2)))
                                    (loop Γ (cdr forms)))]
                            [x (displayln `("Didn't match" ,x)) (error 'todo "~a" x)]))))
          (match (unbox res)
            [(stop where msg)
             (hl-err where)
             (send feedback set-status 'bad)
             (send feedback pprint-message msg)]
            [(go Γ)
             (send feedback set-status
                   (cond
                     [(unbox contains-sheds?)
                      'incomplete]
                     [(let loop ([ctx Γ])
                        (match ctx
                          ['() #f]
                          [(cons (cons x (claim _)) _) #t]
                          [(cons (cons x _) more-ctx) (loop more-ctx)]))
                      'incomplete]
                     [else 'ok]))])
          (prepare-type-info)))))

    (define (on-change)
      (queue-callback
       (thunk
        (define end (send this get-start-position))
        (let loop ([pos (sub1 end)])
          (define (done from)
            (case (send this get-text from end)
              [("Pi")
               (send this insert "Π" from end)]
              [("Sigma")
               (send this insert "Σ" from end)]
              [("lambda")
               (send this insert "λ" from end)]
              [else (void)])
            (void))
          (when (negative? pos)
            (done 0))
          (let* ((str (send this get-text (max pos 0) end)))
            (when (> (string-length str) 0)
              (let ((ch (string-ref str 0)))
                (cond
                  [(or (char-whitespace? ch)
                       (memv ch '(#\( #\) #\[ #\])))
                   (done (add1 pos))]
                  [(>= pos 0) (loop (sub1 pos))]
                  [else (void)])))))
        (send this type-check))
       #f))


    (define/augment (after-delete start len)
      (on-change))

    (define/augment (after-insert start len)
      (on-change))

    (define/public (show-info start end what)
      (send this unhighlight-ranges/key 'type-info)
      (send this highlight-range start end "lightgray" #f 'high #:key 'type-info)
      (match what
        [`(has-type ,t)
         (send feedback reset)
         (send feedback pprint-message `("Has type" ,t))]
        [`(binding-site ,t)
         (send feedback reset)
         (send feedback pprint-message `("Variable binding with type" ,t))]
        [`(is-type ,t)
         (send feedback reset)
         (send feedback pprint-message '("A type"))]
        [`(TODO ,Γ ,t)
         (send feedback reset)
         (send feedback pprint-message `("Will have type" ,t))]
        [_ (void)]))

    (define contains-sheds? (box #f))

    (define/augment (after-set-position)
      (define info
        (interval-map-ref type-info (send this get-start-position) #f))
      (when info
        (show-info (car info) (cadr info) (caddr info))))

    (define type-info (make-interval-map))
    (define type-info-input (box (list)))

    (define (prepare-type-info)
      (define the-info (sort (unbox type-info-input)
                             (lambda (l1 l2)
                               (< (- (cadr l2) (car l2))
                                  (- (cadr l1) (car l1))))))
      (set-box! type-info-input (list))
      (set! type-info (make-interval-map))
      (for ([info (in-list the-info)])
        (interval-map-set! type-info (car info) (cadr info) info)))

    (define (hook loc what)
      (define loc-stx (location->syntax loc))
      (define start (sub1 (source-location-position loc-stx)))
      (define end (sub1 (+ (source-location-position loc-stx)
                           (source-location-span loc-stx))))
      (match what
        ['definition
         (send this change-style (send this definition-name-delta) start end)]
        [`(binding-site ,e)
         (set-box! type-info-input
                   (cons (list start end `(binding-site ,e))
                         (unbox type-info-input)))]
        [`(is-type ,e)
         (set-box! type-info-input
                   (cons (list start end `(is-type ,e))
                         (unbox type-info-input)))]
        [`(has-type ,t)
         (set-box! type-info-input
                   (cons (list start end `(has-type ,t))
                         (unbox type-info-input)))]
        [`(TODO ,Γ ,t)
         (send this highlight-range start end "gold" #f 'low #:key 'TODO)
         (set-box! contains-sheds? #t)
         (set-box! type-info-input
                   (cons (list start end `(TODO ,Γ ,t))
                         (unbox type-info-input)))]
        [_ (void)])
      (void))

    (pie-info-hook hook)

    (queue-callback
     (thunk
      (send this start-colorer
            token-sym->style
            pie-lexer
            (list (list (string->symbol "(") (string->symbol ")"))))
      (send this begin-edit-sequence)
      (send this insert initial-contents)
      (gui:yield)
      (send this type-check)
      (send this end-edit-sequence)
      (send this scroll-to-position 0)))))


(define pie-slide-orientation-horizontal?
  (make-parameter #f))

#;
(define (pie-on-frame f
                      #:initial-contents [contents ""]
                      #:font-size [font-size #f]
                      #:pie-state [pie-state init-st])
  (define panel (new panel:vertical-dragable% [parent f]))
  (send panel set-orientation (pie-slide-orientation-horizontal?))
  (parameterize ([current-pie-gui-font-size (or font-size 40)])
    (define fb (new pie-feedback%))
    (define ed (new pie-text%
                    [feedback fb]
                    [pie-state pie-state]
                    [initial-contents contents]))

    (define c (new editor-canvas% [parent panel] [editor ed] [style '(hide-hscroll auto-vscroll no-border)]))
    (define fbc (new editor-canvas% [parent panel] [editor fb] [style '(hide-hscroll auto-vscroll no-border)]))

    (send panel set-percentages '(2/3 1/3))

    (for ([ed (list fb ed)])
      (define keymap (send ed get-keymap))
      (add-editor-keymap-functions keymap)
      (add-text-keymap-functions keymap)))

  void)

(define frame:pie-text<%>
  (interface (frame:text<%>)))


(define frame:pie-feedback<%>
  (interface (frame:basic<%>)
    [get-pie-feedback (->m (is-a?/c pie-feedback%))]))

(define frame:pie-feedback-mixin
  (mixin (frame:basic<%>) (frame:pie-feedback<%>)
    (super-new)
    (inherit get-area-container)
    (define feedback (new pie-feedback%))
    (define/public (get-pie-feedback)
      feedback)))


(define frame:pie-text-mixin
  (mixin (frame:editor<%> frame:pie-feedback<%>) (frame:pie-text<%>)
    (define f this)
    (define the-editor-class
      (class (editor:backup-autosave-mixin (editor:info-mixin pie-text%))
        (super-new [feedback (send f get-pie-feedback)]
                   [pie-context init-ctx])))
    (super-new [editor% the-editor-class])
    (define/override (get-editor<%>)
      (class->interface pie-text%))))

(define pie-frame%
  (class
    (frame:text-info-mixin
     (frame:info-mixin
      (frame:searchable-text-mixin
       (frame:pie-text-mixin
        (frame:editor-mixin
         (frame:searchable-mixin
          (frame:standard-menus-mixin
           (frame:pie-feedback-mixin
            (frame:size-pref-mixin
             (frame:basic-mixin frame%))))))))))
    (super-new
     [size-preferences-key 'pie:size-prefs]
     [position-preferences-key 'pie:position-prefs])
    (define/override (edit-menu:between-redo-and-cut menu)
      (define increase
        (new menu-item%
             [label "Increase font size"]
             [parent menu]
             [callback
              (lambda (menu event)
                (current-pie-gui-font-size
                 (add1 (current-pie-gui-font-size)))
                (send (send this get-editor) change-style
                      (make-object style-delta% 'change-bigger 1)))]))
      (define decrease
        (new menu-item%
             [label "Decrease font size"]
             [parent menu]
             [callback
              (lambda (menu event)
                (current-pie-gui-font-size
                 (sub1 (current-pie-gui-font-size)))
                (send (send this get-editor) change-style
                      (make-object style-delta% 'change-smaller 1)))]))
      (void))
    (define/override (help-menu:about-callback item evt)
      (message-box
       "About Pie"
       "Welcome to Pie, a little dependently typed language."
       this
       '(ok no-icon)))
    (define/override (get-area-container%)
      panel:horizontal-dragable%)
    (define vertical? (get-preference 'pie:editor-vertical?))
    (send (send this get-area-container)
          set-orientation (not vertical?))
    (define feedback-canvas
      (new editor-canvas%
           [parent (send this get-area-container)]
           [editor (send this get-pie-feedback)]))))

(define (interactive-pie)
  (define icon-size 128)
  (define icon
    (pict->bitmap (scale-to-fit (text "(Π)" null 128) icon-size icon-size)))
  (frame:current-icon icon)
  (application:current-app-name "Pie")
  (frame:setup-size-pref 'pie:size-prefs 600 500
                         #:position-preferences 'pie:position-prefs)
  (current-pie-gui-font-size 16)
  
  (define (new-window filename)
    (define f (new pie-frame%
                   [filename filename]))
    
    (frame:remove-empty-menus f)
    (frame:reorder-menus f)
    (send f show #t)
    f)
  (handler:current-create-new-window new-window)
  (new-window #f))

(module+ main (interactive-pie))
