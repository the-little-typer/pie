#lang racket/base

(require racket/match racket/format racket/port racket/string)

(require "resugar.rkt" "pretty.rkt")

(provide goal->strings indent-string)

;;; This module implements showing TODO goals to users in the format
;;; described in the second recess of The Little Typer.

(define (goal->strings loc Γ t)
  (define hole-summary
    (with-output-to-string
      (lambda ()
        (pprint-pie (resugar t)))))
  (define free-vars
    (for/list ([H Γ]
               #:when (and (pair? H)
                           (pair? (cdr H))
                           (pair? (cadr H))
                           (eqv? (caadr H) 'free)))
      (match-define (list x (list 'free ty)) H)
      (list x ty)))
  (define var-width
    (apply max 0
           (for/list ([b free-vars])
             (string-length (symbol->string (car b))))))
  (define hyps
    (for/list ([b free-vars])
      (match-define (list x ty) b)
      (define padded-x
        (~a x
            #:align 'right
            #:min-width (add1 var-width)
            #:left-pad-string " "))
      (~a
       padded-x
       " : "
       (resugar ty))))
  (define conclusion
    (indent-string 1 hole-summary))
  (define inference-bar
    (make-string
     (apply max 7
            (+ 2 (max-line-length hole-summary))
            (for/list ([h hyps])
              ;; The add1 is to make the line extend at least one
              ;; space past the width of the premise
              (add1 (max-line-length h))))
     #\-))
  (list hole-summary
        (string-join (append (reverse hyps)
                             (list inference-bar
                                   conclusion))
                     "\n")))


(define (indent-string how-much str)
  (define pad (make-string how-much #\space))
  (apply string-append
         (for/list ([line (in-list (string-split str "\n"))])
           (string-append pad line "\n"))))



(define (max-line-length str)
  (apply max 0
         (for/list ([line (in-list (string-split str "\n"))])
           (string-length line))))
