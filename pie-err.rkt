#lang racket/base
(require racket/string racket/port racket/match)
(require "locations.rkt")
(require "resugar.rkt")
(require "pretty.rkt")

(provide (all-defined-out))

(struct exn:fail:pie exn:fail (where)
  #:property prop:exn:srclocs
  (lambda (e)
    (match (exn:fail:pie-where e)
      [(list src line col pos span)
       (list (srcloc src line col pos span))]))
  #:transparent)

(define (raise-pie-error where msg)
  (raise (exn:fail:pie (with-output-to-string
                         (lambda ()
                           (pprint-message msg)))
                       (current-continuation-marks)
                       (location->srcloc where))))
