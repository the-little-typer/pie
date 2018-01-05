#lang typed/racket

(require "basics.rkt" (only-in "normalize.rkt" read-back-ctx val-of-ctx))
;(require racket/match racket/port racket/contract)

(provide dump restore)

(: dump (-> Serializable-Ctx String))
(define (dump v)
  (with-output-to-string
    (lambda ()
      (parameterize ((print-graph #t))
        (write v)))))

(: restore (-> String Serializable-Ctx))
(define (restore str)
  ;; (printf "Restoring:\n\t~v\n\n" str)
  (with-input-from-string str
    (lambda ()
      (define v (read))
      (if (serializable-ctx? v)
          v
          (error 'restore "Invalid deserialized context: ~a" v)))))
