#lang racket/base
(require syntax/srcloc)
(require racket/logging racket/string)
(require (only-in "basics.rkt" var-name?))
(provide attach-tooltip log-all-tooltips!)

;; Tooltip handling for DrRacket. Tooltips are both logged and expanded so that
;; Emacs can get them from the expanded version and DrRacket can get them from
;; the online expander even if there's an error.

(define-logger online-check-syntax)

(define tooltips-queue (box '()))

(define (keyword? x) (and (symbol? x) (not (var-name? x))))

(define (attach-tooltip stx where msg)
  (if (or (and (string? msg) (string=? (string-trim msg) ""))
          (eqv? where #f)
          (not (source-location? where)))
      stx
      (let ([tooltip
             (cond
               [(or (not (syntax? where))
                    (not (pair? (syntax-e where)))
                    (let ([fst (car (syntax-e where))])
                      (and (identifier? fst)
                           (free-identifier=? fst #'quote))))
                (list (vector where
                              (sub1 (source-location-position where))
                              (+ (sub1 (source-location-position where)) (source-location-span where))
                              msg))]
               [(and (syntax? where)
                     (pair? (syntax-e where))
                     (let ([fst (car (syntax-e where))])
                      (and (identifier? fst)
                           (keyword? (syntax-e fst)))))
                (let ([fst (car (syntax-e where))])
                 (list (vector where
                               (sub1 (source-location-position where))
                               (+ (sub1 (source-location-position fst))
                                  (source-location-span fst))
                               msg)
                       (vector where
                               (sub1 (+ (sub1 (source-location-position where))
                                        (source-location-span where)))
                               (+ (sub1 (source-location-position where))
                                  (source-location-span where))
                               msg)))]
               [else
                (list (vector where
                              (sub1 (source-location-position where))
                              (source-location-position where)
                              msg)
                      (vector where
                              (sub1 (+ (sub1 (source-location-position where))
                                       (source-location-span where)))
                              (+ (sub1 (source-location-position where))
                                 (source-location-span where))
                              msg))])])
        (set-box! tooltips-queue (append tooltip (unbox tooltips-queue)))
        (syntax-property stx
                         'mouse-over-tooltips
                         tooltip))))

;; We log all the tooltips at once _after_ type checking to avoid
;; performance issues in DrRacket that occur when logging
;; them individually _during_ type checking.
(define (log-all-tooltips!)
  (log-message online-check-syntax-logger
               'info
               "ignored"
               (list (syntax-property #'(void) 'mouse-over-tooltips (unbox tooltips-queue)))))