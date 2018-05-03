#lang racket/base

(require (for-syntax racket/base racket/match racket/string racket/format)
         (for-syntax (for-syntax racket/base))
         (for-syntax syntax/srcloc))
(require (for-syntax "parser.rkt"))
(require (for-syntax (except-in "basics.rkt" var-name? go-on)))
(require (for-syntax "rep.rkt" "typechecker.rkt" (only-in "normalize.rkt" read-back-ctx)))
(require "basics.rkt" "rep.rkt" "parser.rkt" (only-in "normalize.rkt" val-of-ctx))
(require (for-syntax syntax/parse)
         (for-syntax (for-syntax syntax/parse)))
(require "serialization.rkt")
(require (for-syntax "serialization.rkt"))
(require "pie-err.rkt" (for-syntax "pie-err.rkt"))
(require "resugar.rkt" (for-syntax "resugar.rkt"))
(require "pretty.rkt" (for-syntax "pretty.rkt"))
(require racket/port (for-syntax racket/port))
(require (prefix-in kw: "pie-info.rkt")
         (for-syntax (prefix-in kw: "pie-info.rkt")))

(require (rename-in typed/racket [#%module-begin mod]))

(provide (rename-out [pie-module-begin #%module-begin]
                     [pie-top-interaction #%top-interaction]
                     [pie-top #%top]
                     [pie-datum #%datum])
         (for-syntax (rename-out [pie-top #%top]
                                 [pie-datum #%datum]))
         the-pie-ctx
         list
         match norm
         (rename-out [kw:U U]
                     [kw:Nat Nat] [kw:zero zero] [kw:add1 add1] [kw:which-Nat which-Nat] [kw:iter-Nat iter-Nat] [kw:rec-Nat rec-Nat] [kw:ind-Nat ind-Nat]
                     [kw:-> ->] [kw:→ →] [kw:Π Π] [kw:λ λ] [kw:Pi Pi] [kw:lambda lambda]
                     [kw:quote quote] [kw:Atom Atom]
                     [kw:car car] [kw:cdr cdr] [kw:cons cons] [kw:Σ Σ] [kw:Sigma Sigma] [kw:Pair Pair]
                     [kw:Trivial Trivial] [kw:sole sole]
                     [kw:List List] [kw::: ::] [kw:nil nil] [kw:rec-List rec-List] [kw:ind-List ind-List]
                     [kw:Absurd Absurd] [kw:ind-Absurd ind-Absurd]
                     [kw:= =] [kw:same same] [kw:replace replace] [kw:trans trans] [kw:cong cong] [kw:symm symm]
                     [kw:Vec Vec] [kw:vecnil vecnil] [kw:vec:: vec::] [kw:head head] [kw:tail tail] [kw:ind-Vec ind-Vec]
                     [kw:Either Either] [kw:left left] [kw:right right] [kw:ind-Either ind-Either]
                     [kw:TODO TODO] [kw:the the]
                     [kw:claim claim] [kw:define define] [kw:check-same check-same])
         (all-from-out "pie-info.rkt")
         (for-syntax (all-from-out "pie-info.rkt")))

(begin-for-syntax
  (define-syntax (go-on stx)
    (syntax-parse stx
      [(go-on () e) (syntax/loc stx e)]
      [(go-on ((p0 b0) (p b) ...) e)
       (syntax/loc stx
         (match b0
           [(go p0) (go-on ((p b) ...) e)]
           [(stop where msg) (stop where msg)]))])))

(begin-for-syntax
  (require "tooltip.rkt" (only-in "locations.rkt" location->syntax))
  (define holes (box '()))
  (define (a-or-an t)
    (match t
      [`(,c . ,_)
       (case c
         [(-> → Either = add1 iter-Nat ind-Nat ind-List ind-Absurd ind-Vec ind-Either)
          "an"]
         [else "a"])]
      ['Atom "an"]
      [_ "a"]))
  (define (hook loc what)
    (when (and (not (eqv? loc #f)))
      (define loc-stx (location->syntax loc))
      (define start (sub1 (source-location-position loc-stx)))
      (define end (sub1 (+ (source-location-position loc-stx)
                           (source-location-span loc-stx))))
      (define loc-stx-str
        (let ([src (syntax->datum loc-stx)])
          (let ([test-str (format "~a" src)])
            (if (> (string-length test-str) 40)
                (match src
                  [(cons op args) (format "(~a ...)" op)]
                  [_ (string-append (substring test-str 0 37) "...")])
                test-str))))
      (match what
        ['definition
         (void)]
        [`(binding-site ,t)
         (attach-tooltip #'a-stx loc-stx (format "Variable with type:\n~a"
                                                 (with-output-to-string
                                                   (lambda ()
                                                     (pprint-pie (resugar t))))))]
        [`(is-type ,e)
         (attach-tooltip #'a-stx loc-stx "A type")]
        [`(has-type ,t)
         (let ([sugary (resugar t)])
           (attach-tooltip #'a-stx loc-stx (format "~a\nis ~a:\n~a"
                                                   loc-stx-str
                                                   (a-or-an sugary)
                                                   (with-output-to-string
                                                     (lambda ()
                                                       (pprint-pie sugary))))))]
        [`(TODO ,Γ ,t)
         (let ([sugary (resugar t)])
           (attach-tooltip #'a-stx loc-stx (format "Will be ~a:\n~a"
                                                   (a-or-an sugary)
                                                   (with-output-to-string
                                                     (lambda ()
                                                       (pprint-pie sugary))))))
         (set-box! holes (cons (list loc-stx Γ t) (unbox holes)))]
        [_ (void)])
      (void)))
  (pie-info-hook hook))

(begin-for-syntax
  (struct todo-item (full summary) #:prefab)
  (struct command (name module-path function arguments) #:prefab))

(define-syntax (pie-module-begin stx)
  (syntax-parse stx
    [(_ form ...)
     (define Γ
       (with-handlers ([exn:fail:pie?
                        ;; If there's an error, log all the tooltips we've
                        ;; generated so far so the user gets some feedback.
                        (λ (e) (log-all-tooltips!) (raise e))])
         (let loop ([forms (syntax->list #'(form ...))]
                    [Γ init-ctx])
           (cond
             [(null? forms)
              Γ]
             [else
              (match (parse-pie-decl (car forms))
                [`(claim ,f ,f-loc ,ty)
                 (match (add-claim Γ f f-loc ty)
                   [(go new-Γ)
                    (loop (cdr forms) new-Γ)]
                   [(stop where why)
                    (raise-pie-error where why)])]
                [`(definition ,f ,f-loc ,e)
                 (match (add-def Γ f f-loc e)
                   [(go new-Γ)
                    (loop (cdr forms) new-Γ)]
                   [(stop where why)
                    (raise-pie-error where why)])]
                [`(check-same ,loc ,ty ,e1 ,e2)
                 (match (check-same Γ loc ty e1 e2)
                   [(go _)
                    (loop (cdr forms) Γ)]
                   [(stop where why)
                    (raise-pie-error where why)])]
                [`(expression ,e)
                 (match (norm Γ e)
                   [(go out)
                    (begin (pprint-pie (resugar out))
                           (printf "\n")
                           (loop (cdr forms) Γ))]
                   [(stop where why)
                    (raise-pie-error where why)])])]))))
     (log-all-tooltips!)
     (define ctx-string (dump (read-back-ctx Γ)))
     (with-syntax ([ctx-string ctx-string]
                   [(hole ...)
                    (for/list ([info (reverse (unbox holes))])
                      (match-define (list loc Γ t) info)
                      (define hole-summary
                        (with-output-to-string
                          (lambda ()
                            (pprint-pie (resugar t)))))
                      (define hole-details
                        (let* ([hyps (for/list ([H Γ]
                                                #:when (and (pair? H)
                                                            (pair? (cdr H))
                                                            (pair? (cadr H))
                                                            (eqv? (caadr H) 'free)))
                                       (match-define (list x (list 'free ty)) H)
                                       (~a
                                        (~a x
                                            #:align 'right
                                            #:min-width 8
                                            #:left-pad-string " ")
                                        " : "
                                        (resugar ty)))]
                               [concl hole-summary]
                               [bar (make-string
                                     (apply max 7
                                            (for*/list ([s (cons concl hyps)]
                                                        [l (string-split s "\n")])
                                              (string-length l)))
                                     #\-)])
                          (string-join (append (reverse hyps) (list bar concl)) "\n")))

                      (define hole-output-str
                        (string-append
                         (source-location->prefix loc)
                         (if (ormap (lambda (H)
                                      (match H
                                        [(list _ (list 'free _)) #t]
                                        [_ #f]))
                                    Γ)
                             (string-append "TODO:\n"
                                            hole-details)
                             (string-append "TODO: "
                                            (if (string-contains? hole-summary "\n")
                                                "\n"
                                                "")
                                            hole-summary))
                         "\n"))
                      (syntax-property
                       (syntax-property
                        (quasisyntax/loc loc (displayln #,hole-output-str))
                        'todo
                        (todo-item
                         hole-details
                         hole-summary))
                       'editing-command
                       (list (command "Auto" 'pie/interactive-editing 'auto (list t))
                             (command "More Auto" 'pie/interactive-editing 'more-auto (list t)))))])

       (syntax/loc stx
         (#%module-begin
          (pie-decl->binders form) ...
          (set-box! the-pie-ctx (val-of-ctx (restore ctx-string)))
          (void (list hole ...)))))]))


(define-syntax (pie-top stx)
  (syntax-parse stx
    [(_ . x) #''x]))

(begin-for-syntax
 (define-syntax pie-top
   (syntax-rules ()
     [(_ . x) 'x])))


(define-syntax (pie-datum stx)
  (syntax-parse stx
    [(_ . x) #''x]))

(begin-for-syntax
  (define-syntax pie-datum
    (syntax-rules ()
      [(_ . x) 'x])))

(define the-pie-ctx (box init-ctx))

(define-syntax (pie-top-interaction stx)
  (syntax-parse stx
    [(_ . e)
     (syntax/loc stx
       (match (parse-pie-decl #'e)
         [`(expression ,expr)
          (define Γ (unbox the-pie-ctx))
          (define n (norm Γ expr))
          (match n
           [(go out)
            (pprint-pie (resugar out))]
           [(stop where what)
            (raise-pie-error where what)])]
         [`(check-same ,loc ,ty ,e1 ,e2)
          (match (check-same (unbox the-pie-ctx) loc ty e1 e2)
            [(go _)
             (void)]
            [(stop where why)
             (raise-pie-error where why)])]
        [_ (raise-syntax-error #f "The Pie REPL does not support adding new definitions. Please load a file containing Pie code." #'e)]))]))

(module reader syntax/module-reader
  pie
  #:info (lambda (k v default-filter)
           (case k
             [(drracket:default-filters)
              '(("Pie Sources" "*.pie"))]
             [(drracket:default-extension)
              "pie"]
             [(drracket:opt-out-toolbar-buttons)
              '(debug-tool)]
             [(drracket:indentation)
              (lambda (txt pos)
                (and-let* ([line (send txt position-paragraph pos)]
                           [line-start (send txt paragraph-start-position line)]
                           [sexp-start (send txt find-up-sexp line-start)]
                           [buffer-end-pos (send txt last-position)]
                           [op-end (send txt get-forward-sexp (add1 sexp-start))]
                           [op-start (send txt get-backward-sexp op-end)]
                           [indent-basis
                            (- op-start
                               (send txt paragraph-start-position
                                     (send txt position-paragraph op-start)))]
                           [default-indent (+ 1 indent-basis)]
                           [op (string->symbol (send txt get-text op-start op-end #t))])
                          (define in-Pi-or-Sigma?
                            (and-let* ([grandparent-sexp-start (send txt find-up-sexp sexp-start)]
                                       [grand-op-end (send txt get-forward-sexp (add1 grandparent-sexp-start))]
                                       [grand-op-start (send txt get-backward-sexp grand-op-end)]
                                       [grand-op (send txt get-text grand-op-start grand-op-end)])
                                      (if (member grand-op '("Pi" "Π" "Sigma" "Σ"))
                                          #t
                                          #f)))
                          (define real-op
                            (match op
                              ['lambda 'λ]
                              ['Pi 'Π]
                              ['Sigma 'Σ]
                              ['-> '→]
                              [other other]))

                          (match real-op
                            [(or 'which-Nat 'iter-Nat 'rec-Nat 'ind-Nat
                                 'car 'cdr 'rec-List 'ind-List 'ind-Absurd
                                 'replace 'cong 'trans 'symm 'head 'tail 'ind-Vec
                                 'ind-Either)
                             (define target-count
                               (match real-op
                                 [(or 'trans 'ind-Vec) 2]
                                 [_ 1]))
                             ;; find if last
                             (let ([targets-end
                                    (let loop ([i target-count]
                                               [pos (add1 sexp-start)])
                                      (if (> i 0)
                                          (loop (sub1 i)
                                                (send txt get-forward-sexp pos))
                                          pos))])
                               (and targets-end
                                    (let ([first-line-sexp-end (send txt get-forward-sexp pos)])
                                      (if (or (not first-line-sexp-end)
                                              (>= first-line-sexp-end targets-end))
                                          (+ 1 indent-basis)
                                          (+ 4 indent-basis)))))]
                            [other
                             #:when (or (eqv? op '->) (eqv? op '→))
                             (and-let* ([sexp-end (send txt get-forward-sexp sexp-start)]
                                        [last-arg-start (send txt get-backward-sexp (sub1 sexp-end))]
                                        [first-arg-start (send txt get-backward-sexp
                                                               (send txt get-forward-sexp op-end))]
                                        [last-arg-end (send txt get-forward-sexp last-arg-start)]
                                        [first-line-sexp-end (send txt get-forward-sexp pos)]
                                        [->-indent-basis
                                         (- first-arg-start
                                            (send txt paragraph-start-position
                                                  (send txt position-paragraph first-arg-start)))])
                                       (if (>= first-line-sexp-end last-arg-end)
                                           (+ 1 indent-basis)
                                           (+ ->-indent-basis)))]
                            [_
                             #:when in-Pi-or-Sigma?
                             ;; Use normal Racket sexp indenting
                             #f]
                            [_ default-indent])))]
             [(color-lexer)
              (lambda (in)
                (define-values (tok pie-style paren start end) (pie-lexer in))
                (values tok
                        (case pie-style
                          [(type-ctor data-ctor) 'constant]
                          [else pie-style])
                        paren
                        start
                        end))]
             [else (default-filter k v)]))
  (require "gui/pie-lexer.rkt")
  (require racket/class racket/match)
  (require (for-syntax racket/base syntax/parse))
  (define-syntax (and-let* stx)
    (syntax-parse stx
      [(_ () e ...) #'(let () e ...)]
      [(_ ((x:id e1) (y:id e2) ...) e ...)
       #'(let ((x e1))
           (and x (and-let* ((y e2) ...) e ...)))]))
)

