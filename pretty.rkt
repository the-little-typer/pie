#lang racket/base


(require racket/function racket/list racket/match)

(require "resugar.rkt")

(provide pprint-pie pprint-message indented)

(define indentation (make-parameter 0))

(define-syntax indented
  (syntax-rules ()
    [(_ i e ...)
     (parameterize ([indentation (+ i (indentation))])
       (begin e ...))]))

(define (spaces n)
  (for ([i (in-range n)])
    (printf " ")))

(define (space) (spaces 1))

(define (indent)
  (spaces (indentation)))

(define (start-line)
  (indent))

(define (terpri)
  (printf "\n")
  (start-line))

(define (l)
  (printf "("))

(define (r)
  (printf ")"))

(define-syntax parens
  (syntax-rules ()
    ((_ e ...)
     (begin (l)
            (indented 1 e ...)
            (r)))))

(define (top-binder? sym)
  (and (symbol? sym)
       (or (eqv? sym '?)
           (eqv? sym 'Pi)
           (eqv? sym 'Π)
           (eqv? sym 'Sigma)
           (eqv? sym 'Σ))))

(define (ind? sym)
  (and (symbol? sym)
       (let ([str (symbol->string sym)])
         (and (>= (string-length str) 4)
              (string=? (substring str 0 4) "ind-")))))

(define (simple-elim? sym)
  (and (symbol? sym)
       (or (eqv? sym 'which-Nat)
           (eqv? sym 'iter-Nat)
           (let ([str (symbol->string sym)])
             (and (>= (string-length str) 4)
                  (string=? (substring str 0 4) "rec-"))))))

(define (sep s op args)
  (match args
    ['() (void)]
    [(list b) (op b)]
    [(cons b bs) (op b) (s) (sep s op bs)]))

(define (vsep op args)
  (sep terpri op args))
(define (hsep op args)
  (sep space op args))

(define (annots bindings)
  (define (print-binding b)
    (match b
      [(list (app symbol->string x) ty)
       (parens
        (printf x)
        (space)
        (indented (+ (string-length x) 2)
                  (print-pie ty)))]))
  (vsep print-binding bindings))

(define (atomic? x)
  (match x
    [(? symbol?) #t]
    [(? number?) #t]
    [(list 'quote _) #t]
    [_ #f]))

;; Print a high-level Pie expression
(define (print-pie expr)
  ;; Always display something, even if the print code is borked
  (with-handlers ([exn:fail? (lambda (e)
                               (display expr))])
   (match expr
     [(list (? top-binder? (app symbol->string binder-string))
            bindings
            body)
      (parens (printf binder-string)
              (spaces 1)
              (indented (add1 (string-length binder-string))
                        (parens (annots bindings)))
              (terpri)
              (print-pie body))]
     [(list (or 'lambda 'λ) (list-rest args) body)
      (parens
       (display 'λ) (space) (parens (hsep display args))
       (indented 1 (terpri) (print-pie body)))]
     [(cons (or '-> '→) (app reverse (cons ret (app reverse args))))
      (parens (display "→")
              (if (andmap atomic? args)
                  (begin (space)
                         (hsep display args))
                  (indented 3
                            (space)
                            (vsep print-pie
                                  args)))
              (indented 1 (terpri) (print-pie ret)) )]
     [(list 'quote x) (printf "'~a" x)]
     [(cons (and op (? ind? (app symbol->string elim))) args)
      (define target-count
        (case op
          [(ind-Vec trans) 2]
          [else 1]))
      (define-values (targets normal)
        (split-at args target-count))
      (parens
       (display elim)
       (space)
       (hsep print-pie targets)
       (match normal
         [(list) (void)]
         [(cons motive others)
          (indented 2 (terpri) (vsep print-pie (cons motive others)))]))]
     [(cons (and op (? simple-elim? (app symbol->string elim))) args)
      (match-define (cons target normal) args)
      (parens
       (display elim)
       (space)
       (print-pie target)
       (match normal
         [(list) (void)]
         [others
          (indented 2
                    (terpri)
                    (vsep print-pie others))]))]
     [(list-rest (? symbol? op) (? atomic? arg) args)
      #:when (and (< (length args) 20)
                  (andmap atomic? args))
      (parens
       (hsep print-pie
             (cons op (cons arg args))))]
     [(list-rest (? symbol? op) arg args)
      (parens (print-pie op) (space)
              (indented (add1 (string-length (symbol->string op)))
                        (print-pie arg))
              (indented 1
                        (when (pair? args)
                          (terpri)
                          (vsep print-pie
                                args))))]
     [(list-rest op args)
      (parens (print-pie op)
              (indented 1
                        (terpri)
                        (vsep print-pie args)))]
     [other (display other)])))

(define (pprint-pie expr (description ""))
  (start-line)
  (indented (string-length description)
            (when (not (string=? description ""))
              (display description))
            (print-pie expr)))

(define (pprint-claim  name ty)
  (start-line)
  (parens
   (indented 1
             (display 'claim) (space) (display name) (terpri)
             (print-pie ty))))

(define (pprint-message msg)
  (start-line)
  (for ([part (in-list msg)])
    (cond [(string? part)
           (display part)]
          [(symbol? part)
           (space)
           (display part)
           (space)]
          [else (indented 2 (terpri) (print-pie (resugar part))) (terpri)])))
