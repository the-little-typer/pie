#lang racket/base
(provide location?
         syntax->location
         (rename-out [location-syntax location->syntax])
         location->srcloc
         location-for-info?
         not-for-info)

(struct location (syntax for-info?))

(define (syntax->location stx)
  (location stx #t))

(define (not-for-info loc)
  (location (location-syntax loc) #f))

(define (location->srcloc loc)
  (define stx (location-syntax loc))
  (list (format "~a" (syntax-source stx))
        (syntax-line stx)
        (syntax-column stx)
        (syntax-position stx)
        (syntax-span stx)))
