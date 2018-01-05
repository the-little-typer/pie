#lang racket/base
(require (for-syntax racket/base syntax/parse))

(provide (all-defined-out))

(define-syntax (define-pie-keyword stx)
  (syntax-parse stx
    [(_ kw:id)
     #'(define-syntax (kw inner-stx)
         (syntax-parse inner-stx
           #:literals (kw)
           [kw #'(void)]
           [(kw e (... ...)) #'(void e (... ...))]))]))

(define-syntax (define-pie-keywords stx)
  (syntax-parse stx
    [(_ kw:id ...)
     #'(begin
         (define-pie-keyword kw)
         ...)]))

(define-pie-keywords
  U
  Nat zero add1 which-Nat iter-Nat rec-Nat ind-Nat
  -> → Π λ Pi lambda
  quote Atom
  car cdr cons Σ Sigma Pair
  Trivial sole
  List :: nil rec-List ind-List
  Absurd ind-Absurd
  = same replace trans cong symm ind-=
  Vec vecnil vec:: head tail ind-Vec
  Either left right ind-Either
  TODO the
  check-same claim define)
