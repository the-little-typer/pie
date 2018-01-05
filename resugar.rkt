#lang racket/base

(require racket/match)
(require (only-in "basics.rkt" var-name?))

(provide resugar)

(define (resugar ll-term)
  (cdr (resugar* ll-term)))

(define (resugar* ll-term)
  (match ll-term
    [`U
     (cons '() 'U)]
    [`(TODO . ,_)
     (cons '() 'TODO)]
    [`zero
     (cons '() 0)]
    [`(add1 ,n)
     (let ([resugared-n (resugar* n)])
       (cons (car resugared-n)
             (if (or (eqv? (cdr resugared-n) 0)
                     (positive-number? (cdr resugared-n)))
                 (add1 (cdr resugared-n))
                 `(add1 ,(cdr resugared-n)))))]
    [`',sym
     (cons '() `',sym)]
    [(? symbol? x)
     (if (pie-keyword? x)
         (cons '() x)
         (cons `(,x) x))]
    [`(λ (,x) ,result)
     (let ((resugared (resugar* result)))
       (cons (remv* `(,x) (car resugared))
             (add-λ x (cdr resugared))))]
    [`(Π ((,x ,arg-type)) ,result-type)
     (let ((arg (resugar* arg-type))
           (res (resugar* result-type)))
       (if (memv x (car res))
           (cons (append (car arg) (remv* `(,x) (car res)))
                 (add-Π x (cdr arg) (cdr res)))
           (cons (append (car arg) (car res))
                 (add--> (cdr arg) (cdr res)))))]
    [`(Σ ((,x ,car-type)) ,cdr-type)
     (let ((a-t (resugar* car-type))
           (d-t (resugar* cdr-type)))
       (if (memv x (car d-t))
           (cons (append (car a-t) (remv* `(,x) (car d-t)))
                 (add-Σ x (cdr a-t) (cdr d-t)))
           (cons (append (car a-t) (car d-t))
                 `(Pair ,(cdr a-t) ,(cdr d-t)))))]
    [`(:: ,hd (nil))
     (let ((hd-out (resugar* hd)))
       (cons (car hd-out)
             `(list ,(cdr hd-out))))]
    [`(:: ,hd ,tl)
     (let ([resugared-hd (resugar* hd)]
           [resugared-tl (resugar* tl)])
       (cons (append (car resugared-hd) (car resugared-tl))
             (if (and (pair? (cdr resugared-tl))
                      (eqv? (car (cdr resugared-tl))
                            'list))
                 `(list ,(cdr resugared-hd) . ,(cdr (cdr resugared-tl)))
                 `(:: ,(cdr resugared-hd) ,(cdr resugared-tl)))))]
    [`(vec:: ,hd (vecnil))
     (let ((hd-out (resugar* hd)))
       (cons (car hd-out)
             `(vec ,(cdr hd-out))))]
    [`(vec:: ,hd ,tl)
     (let ([resugared-hd (resugar* hd)]
           [resugared-tl (resugar* tl)])
       (cons (append (car resugared-hd) (car resugared-tl))
             (if (and (pair? (cdr resugared-tl))
                      (eqv? (car (cdr resugared-tl))
                            'list))
                 `(vec ,(cdr resugared-hd) . ,(cdr (cdr resugared-tl)))
                 `(vec:: ,(cdr resugared-hd) ,(cdr resugared-tl)))))]
    [`(replace ,t ,tgt ,mot ,base)
     (let ((resugared-t (resugar* t))
           (resugared-tgt (resugar* tgt))
           (resugared-mot (resugar* mot))
           (resugared-base (resugar* base)))
       (cons (append (car resugared-t) (car resugared-tgt) (car resugared-mot) (car resugared-base))
             `(replace (the ,(cdr resugared-t) ,(cdr resugared-tgt))
                       ,(cdr resugared-mot)
                       ,(cdr resugared-base))))]
    [`(cong ,t ,tgt ,fun)
     (let ((resugared-tgt (resugar* tgt))
           (resugared-fun (resugar* fun)))
       (cons (append (car resugared-tgt) (car resugared-fun))
             `(cong ,(cdr resugared-tgt)
                    ,(cdr resugared-fun))))]
    [`(,kw . ,args)
     #:when (pie-keyword? kw)
     (let ((resugared-args (map (lambda (arg) (resugar* arg)) args)))
       (cons (apply append (map car resugared-args))
             `(,kw . ,(map cdr resugared-args))))]
    [`(,op ,arg)
     (let ([resugared-op (resugar* op)]
           [resugared-arg (resugar* arg)])
       (cons (append (car resugared-op) (car resugared-arg))
             (cond [(not (pair? (cdr resugared-op)))
                    `(,(cdr resugared-op) ,(cdr resugared-arg))]
                   [(pie-keyword? (car (cdr resugared-op)))
                    `(,(cdr resugared-op) ,(cdr resugared-arg))]
                   [else
                    (append (cdr resugared-op) `(,(cdr resugared-arg)))])))]
;;; Resugaring should never crash, no matter how odd the code is
    [`,any-term (cons '() any-term)]))

(define (add-λ x term)
  (match term
    [`(λ ,xs ,result)
     `(λ (,x . ,xs) ,result)]
    [`,non-λ
     `(λ (,x) ,non-λ)]))

(define (add-Π x arg-type term)
  (match term
    [`(Π ,args ,result-type)
     `(Π ((,x ,arg-type) . ,args) ,result-type)]
    [`,non-Π
     `(Π ((,x ,arg-type)) ,non-Π)]))

(define (add--> arg-type term)
  (match term
    [`(→ . ,types)
     `(→ ,arg-type . ,types)]
    [`,non-->
     `(→ ,arg-type ,non-->)]))

(define (add-Σ x arg-type term)
  (match term
    [`(Σ ,args ,result-type)
     `(Σ ((,x ,arg-type) . ,args) ,result-type)]
    [`,non-Σ
     `(Σ ((,x ,arg-type)) ,non-Σ)]))

(define (add-? x hole-type term)
  (match term
    [`(? ,args ,body)
     `(? ((,x ,hole-type) . ,args) ,body)]
    [`,non-?
     `(? ((,x ,hole-type)) ,non-?)]))


(define (positive-number? x)
  (exact-positive-integer? x))

(define (quoted-symbol? term)
  (match term
    [`',x (legal-symbol? x)]
    [`,non-x #f]))

(define (legal-symbol? sym)
  (and (symbol? sym)
       (all-symbol-char? (string->list (symbol->string sym)))))

(define (all-symbol-char? chars)
  (cond
    [(null? chars)
     #t]
    [(symbol-char? (car chars))
     (all-symbol-char? (cdr chars))]
    [(not (symbol-char? (car chars)))
     #f]))

(define (symbol-char? char)
  (or (char-alphabetic? char)
      (char=? char #\-)))

(define (pie-keyword? x)
  (and (symbol? x) (not (var-name? x))))
