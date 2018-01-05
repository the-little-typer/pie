#lang typed/racket/base

;;; This module contains utilities for interacting with Pie from the
;;; Racket REPL and in test suites.

(require "basics.rkt")
(require "typechecker.rkt")
(require "normalize.rkt")
(require racket/match)
(provide (all-defined-out))

(: norm-type (-> Ctx Src (Perhaps Core)))
(define (norm-type Γ e)
  (go-on ((e-out (is-type Γ e)))
    (go (read-back-type Γ (val-in-ctx Γ e-out)))))

(: rep (-> Ctx Src (Perhaps (List 'the Core Core))))
(define (rep Γ e)
  (go-on ((`(the ,t-out ,e-out) (synth Γ e)))
    (let ((tv (val-in-ctx Γ t-out))
          (v (val-in-ctx Γ e-out)))
      (go `(the ,(read-back-type Γ tv)
                ,(read-back Γ tv v))))))

(: norm (-> Ctx Src (Perhaps Core)))
(define (norm Γ e)
  (match (go-on ((`(the ,t-out ,e-out) (synth Γ e)))
                (let ((tv (val-in-ctx Γ t-out))
                      (v (val-in-ctx Γ e-out)))
                  (go `(the ,(parameterize ([unfold-defs? #f])
                               (read-back-type Γ tv))
                            ,(read-back Γ tv v)))))
    [(go e) (go e)]
    [(stop where msg)
     (match (norm-type Γ e)
       [(go out) (go out)]
       [_ (stop where msg)])]))


(: type-or-expr (-> Ctx Src (Perhaps Ctx)))
(define (type-or-expr Γ e)
  (match (rep Γ e)
    [(go out)
     (begin (displayln out)
            (go Γ))]
    [(stop where msg)
     (match (norm-type Γ e)
       [(go out) (begin (displayln out) (go Γ))]
       [_ (stop where msg)])]))

(: check-same (-> Ctx Loc Src Src Src (Perhaps Void)))
(define (check-same Γ loc t a b)
  (go-on ((t-out (is-type Γ t))
          (tv (go (val-in-ctx Γ t-out)))
          (a-out (check Γ a tv))
          (b-out (check Γ b tv))
          (av (go (val-in-ctx Γ a-out)))
          (bv (go (val-in-ctx Γ b-out))))
    (convert Γ loc tv av bv)))



