#lang racket/base
(require racket/match racket/format)
(provide auto more-auto)

(define (auto type)
  (~a (auto-aux 1 type)))

(define (more-auto type)
  (~a (auto-aux 50 type)))

(define (auto-aux depth type)
  (if (zero? depth)
      'TODO
      (match type
        [`(Π ((,x ,A)) ,B)
         `(λ (,x) ,(auto-aux (sub1 depth) B))]
        [`(Σ ((,x ,A)) ,D)
         `(cons ,(auto-aux (sub1 depth) A)
                ,(auto-aux (sub1 depth) D))]
        ['Trivial 'sole]
        [`(Vec ,E zero) 'vecnil]
        [`(Vec ,E (add1 ,len))
         `(vec:: ,(auto-aux (sub1 depth) E)
                 ,(auto-aux (sub1 depth) `(Vec ,E ,len)))]
        [else 'TODO])))
