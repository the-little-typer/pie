#lang racket/base

(require racket/function racket/list racket/match)
(require "pie-styles.rkt" "../basics.rkt" "../resugar.rkt")
(require racket/gui framework)
(require pict)

(provide pie-feedback%)

(define indentation (make-parameter 0))

(define-syntax indented
  (syntax-rules ()
    [(_ i e ...)
     (parameterize ([indentation (+ i (indentation))])
       (begin e ...))]))

(define pie-feedback%
  (class (pie-styles-mixin color:text%)
    (super-new [auto-wrap #t])

    (init-field [status 'unknown])

    (define ok (colorize (text "✔" "DejaVu Sans Mono" (current-pie-gui-font-size)) "darkgreen"))
    (define incomplete
      (let* ([mark (colorize (text "?" (cons 'bold "DejaVu Sans Mono") (current-pie-gui-font-size)) "white")]
             [size (max (pict-width mark) (pict-height mark))])
        (cc-superimpose
         (filled-rounded-rectangle size size #:color "gold" #:draw-border? #f)
         mark)))
    (define bad (colorize (text "✖" "DejaVu Sans Mono" (current-pie-gui-font-size)) "red"))
    (define/public (set-status s)
      (set! status s)
      (send this invalidate-bitmap-cache)
      (define c (send this get-canvas))
      (when c (send c refresh)))
    (define (status-pict)
      (match status
        ['ok ok]
        ['incomplete incomplete]
        ['bad bad]
        [_ (blank)]))

    (define/override (on-paint before? dc left top right bottom dx dy draw-caret)
      (super on-paint before? dc left top right bottom dx dy draw-caret)
      (define pict (status-pict))
      (define c (send this get-canvas))
      (when c
        (define w (send c get-width))
        (draw-pict pict dc (- w (pict-width pict) 25 (send c horizontal-inset)) (+ 5 (send c vertical-inset)))))

    (define-syntax unlocked
      (syntax-rules ()
        [(_ e ...)
         (let ((locked? (send this is-locked?)))
           (dynamic-wind
             (thunk (when locked? (send this lock #f)))
             (thunk e ...)
             (thunk (when locked? (send this lock #t)))))]))

    (define/public (set-error e)
      (unlocked
       (send this reset)
       (send this change-style (send this text-style))
       (send this insert (exn-message e) 0 (send this last-position)))
      (send this scroll-to-position 0))

    (define/public (reset)
      (unlocked
       (send this insert "" 0 (send this last-position))
       (send this change-style (send this text-style))))

    (define/public (spaces n)
      (send this change-style (send this text-style))
      (send this insert (build-string n (lambda (i) #\space))))

    (define/public (space) (spaces 1))

    (define/public (indent)
      (spaces (indentation)))

    (define/public (start-line)
      (indent))

    (define/public (terpri)
      (send this change-style (send this text-style))
      (send this insert "\n")
      (start-line))

    (define (l)
      (send this change-style (send this parenthesis-style))
      (send this insert "(")
      (send this change-style (send this text-style)))

    (define (r)
      (send this change-style (send this parenthesis-style))
      (send this insert ")")
      (send this change-style (send this text-style)))

    (define-syntax parens
      (syntax-rules ()
        ((_ e ...)
         (begin (l)
                (indented 1 e ...)
                (r)))))

    (define-syntax η
      (syntax-rules ()
        [(η x) (lambda () (x))]))

    (define (top-binder? sym)
      (and (symbol? sym)
           (or (eqv? sym 'Pi)
               (eqv? sym 'Π)
               (eqv? sym 'Sigma)
               (eqv? sym 'Σ))))
    (define (ind? sym)
      (and (symbol? sym)
           (let ([str (symbol->string sym)])
             (and (>= (string-length str) 4)
                  (string=? (substring str 0 4) "ind-")))))

    (define (sep s op args)
      (match args
        ['() (void)]
        [(list b) (op b)]
        [(cons b bs) (op b) (s) (sep s op bs)]))


    (define (vsep op args)
      (sep (η terpri) op args))
    (define (hsep op args)
      (sep (η space) op args))

    (define (annots bindings)
      (define (print-binding b)
        (match b
          [(list x ty)
           (parens
            (print-var x)
            (space)
            (indented (+ (string-length (symbol->string x)) 2)
                      (print-pie ty)))]))
      (vsep print-binding bindings))

    (define (atomic? x)
      (match x
        [(? symbol?) #t]
        [(? number?) #t]
        [(list 'quote _) #t]
        [_ #f]))

    (define/public (print-tycon c)
      (send this change-style (send this type-constructor-style))
      (send this insert (symbol->string c))
      (send this change-style (send this text-style)))

    (define/public (print-con c)
      (send this change-style (send this data-constructor-style))
      (send this insert (symbol->string c))
      (send this change-style (send this text-style)))

    (define/public (print-atom c)
      (send this change-style (send this data-constructor-style))
      (send this insert "'")
      (send this insert (symbol->string c))
      (send this change-style (send this text-style)))

    (define/public (print-lit x)
      (send this change-style (send this data-constructor-style))
      (send this insert (format "~a" x))
      (send this change-style (send this text-style)))

    (define/public (print-elim c)
      (send this change-style (send this keyword-style))
      (send this insert (symbol->string c))
      (send this change-style (send this text-style)))

    (define/public (print-var c)
      (send this change-style (send this var-style))
      (send this insert (symbol->string c))
      (send this change-style (send this text-style)))

    (define (elim? x)
      (if (memv x '(which-Nat ind-Nat iter-Nat rec-Nat ind-Vec head tail car cdr ind-Absurd the))
          #t
          #f))

    (define (tycon? x)
      (if (memv x '(U Π Pi Σ Sigma Nat Atom Absurd Trivial Pair -> Vec List Either))
          #t
          #f))

    (define (con? x)
      (if (memv x '(cons λ lambda add1 zero :: vec:: nil vecnil sole left right))
          #t
          #f))

    (define (print-pie expr)
      ;; Always display something, even if the print code is borked
      (with-handlers ([exn:fail? (lambda (e)
                                   (displayln (exn-message e))
                                   (send this insert (format "~a" expr)))])
        (match expr
          [(list (and b (or 'Π 'Σ))
                 bindings
                 body)
           (parens (print-tycon b)
                   (spaces 1)
                   (indented (add1 (string-length (symbol->string b)))
                             (parens (annots bindings)))
                   (terpri)
                   (print-pie body))]
          [(list (or 'lambda 'λ) (list-rest args) body)
           (parens
            (print-con 'λ) (space) (parens (hsep (lambda (x) (print-var x)) args))
            (indented 1 (terpri) (print-pie body)))]
          [(cons '-> (app reverse (cons ret (app reverse args))))
           (parens (print-tycon '->)
                   (if (andmap atomic? args)
                       (begin (space)
                              (hsep print-pie args))
                       (indented 3
                                 (space)
                                 (vsep (lambda (x) (print-pie x))
                                       args)))
                   (indented 1 (terpri) (print-pie ret)) )]
          [(list 'quote x) (print-atom x)]
          [(list 'TODO loc ty) (print-elim 'TODO)]
          [(cons (? elim? e) args)
           (parens
            (print-elim e)
            (space)
            (match args
              [(list) (void)]
              [(cons target others)
               (indented (+ (string-length (symbol->string e)) 1)
                         (print-pie target))
               (when (pair? others)
                 (indented 2
                           (terpri)
                           (vsep (lambda (x) (print-pie x)) others)))]))]
          [(cons (? con? c) args)
           (parens (print-con c)
                   (space)
                   (match args
                     [(list) (void)]
                     [(list (? atomic? arg))
                      (print-pie arg)]
                     [(list arg)
                      (indented 2
                                (terpri)
                                (print-pie arg))]
                     [(cons fst others)
                      (indented (+ (string-length (symbol->string c)) 1)
                                (print-pie fst))
                      (indented 2
                                (terpri)
                                (vsep (lambda (x) (print-pie x)) others))]))]
          [(list-rest (? symbol? op) (? atomic? arg) args)
           #:when (and (< (length args) 20)
                       (andmap atomic? args))
           (parens
            (hsep (lambda (x)
                    (print-pie x))
                  (cons op (cons arg args))))]
          [(list-rest (? symbol? op) arg args)
           (parens (print-pie op) (space)
                   (indented (add1 (string-length (symbol->string op)))
                             (print-pie arg))
                   (indented 1
                             (when (pair? args)
                               (terpri)
                               (vsep (lambda (x) (print-pie x))
                                     args))))]
          [(list-rest op args)
           (parens (print-pie op)
                   (indented 1
                             (terpri)
                             (vsep (lambda (x) (print-pie x))
                                   args)))]
          [(? con? c)
           (print-con c)]
          [(? tycon? t)
           (print-tycon t)]
          [(? symbol? x)
           (print-var x)]
          [(? number? n)
           (print-lit n)]
          [other (send this insert (format "OOPS[~a]" other))])))

    (define/public (pprint-pie expr (description ""))
      (unlocked
       (start-line)
       (indented (string-length description)
                 (when (not (string=? description ""))
                   (send this change-style (send this text-style))
                   (send this insert description))
                 (print-pie (resugar expr))))
      (send this scroll-to-position 0))

    (define/public (pprint-message msg)
      (unlocked
       (start-line)
       (for ([part msg])
         (cond [(string? part)
                (send this change-style (send this text-style))
                (send this insert part)]
               [else (indented 2 (terpri) (print-pie (resugar part))) (terpri)])))
      (send this scroll-to-position 0))

    (send this lock #t)))







