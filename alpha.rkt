#lang typed/racket

(require "basics.rkt")

(provide α-equiv?)

;; Public interface

(: α-equiv? (-> Core Core Boolean))
(define (α-equiv? e1 e2)
  (α-equiv-aux 0 '() '() e1 e2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helpers

(define-type Bindings (Listof (Pair Symbol Natural)))

(: bind (-> Bindings Symbol Natural Bindings))
(define (bind b x lvl)
  (cons (cons x lvl)
        b))

(: α-equiv-aux (-> Natural Bindings Bindings Core Core Boolean))
(define (α-equiv-aux lvl b1 b2 e1 e2)
  (match* (e1 e2)
    [(x y)
     #:when (and (symbol? x) (symbol? y))
     (cond
       [(and (var-name? x) (var-name? y))
        (let ([x-binding (assv x b1)]
              [y-binding (assv y b2)])
          (match* (x-binding y-binding)
            ;; Both bound
            [((cons _ lvl-x) (cons _ lvl-y))
             (= lvl-x lvl-y)]
            ;; Both free
            [(#f #f) (eqv? x y)]
            ;; One bound, one free
            [(_ _) #f]))]
       ;; Constructor equality (e.g. zero ≡ zero)
       [(and (not (var-name? x)) (not (var-name? y)))
        (eqv? x y)]
       ;; one constructor, one var (e.g. zero /≡ x)
       [else #f])]
    ;; Atoms must be the same atom
    [(`(quote ,a) `(quote ,b))
     (eqv? a b)]
    [(`(Π ((,x ,A1)) ,B1) `(Π ((,y ,A2)) ,B2))
     (and (α-equiv-aux lvl b1 b2 A1 A2)
          (α-equiv-aux (add1 lvl)
                       (bind b1 x lvl)
                       (bind b2 y lvl)
                       B1
                       B2))]
    [(`(Σ ((,x ,A1)) ,D1) `(Σ ((,y ,A2)) ,D2))
     (and (α-equiv-aux lvl b1 b2 A1 A2)
          (α-equiv-aux (add1 lvl)
                       (bind b1 x lvl)
                       (bind b2 y lvl)
                       D1
                       D2))]
    [(`(λ (,x) ,body1) `(λ (,y) ,body2))
     (α-equiv-aux (add1 lvl)
                  (bind b1 x lvl)
                  (bind b2 y lvl)
                  body1
                  body2)]
    ;; η for Absurd relies on read-back inserting an annotation
    [(`(the Absurd ,_) `(the Absurd ,_)) #t]
    ;; Non-binding keywords
    [((cons kw1 args1)
      (cons kw2 args2))
     #:when (and (symbol? kw1) (symbol? kw2)
                 (not (or (eqv? kw1 'λ) (eqv? kw1 'Π) (eqv? kw1 'Σ) (eqv? kw1 'TODO)))
                 (not (or (eqv? kw2 'λ) (eqv? kw2 'Π) (eqv? kw2 'Σ) (eqv? kw2 'TODO)))
                 (not (var-name? kw1)) (not (var-name? kw2)))
     (and (eqv? kw1 kw2)
          (α-equiv-aux* lvl b1 b2 args1 args2))]
    ;; Holes from the same location are equal
    [(`(TODO ,loc1 ,t1) `(TODO ,loc2 ,t2))
     (and (equal? loc1 loc2)
          (α-equiv-aux lvl b1 b2 t1 t2))]
    ;; Function application
    [(`(,f ,arg1) `(,g ,arg2))
     (and (α-equiv-aux lvl b1 b2 f g)
          (α-equiv-aux lvl b1 b2 arg1 arg2))]
    [(_ _) #f]))


(: α-equiv-aux* (-> Natural Bindings Bindings (Listof Core) (Listof Core) Boolean))
(define (α-equiv-aux* lvl b1 b2 args1 args2)
  (cond
    [(and (pair? args1) (pair? args2))
     (and (α-equiv-aux lvl b1 b2 (car args1) (car args2))
          (α-equiv-aux* lvl b1 b2 (cdr args1) (cdr args2)))]
    [(and (null? args1) (null? args2)) #t]
    [else #f]))

(module+ test
  (require typed/rackunit)
  (check-true (α-equiv? '(λ (x) x) '(λ (x) x)))
  (check-true (α-equiv? '(λ (x) x) '(λ (y) y)))
  (check-true (α-equiv? '(λ (x) (λ (y) x)) '(λ (x) (λ (y) x))))
  (check-true (α-equiv? '(λ (x) (λ (y) x)) '(λ (y) (λ (z) y))))
  (check-false (α-equiv? '(λ (x) (λ (y) x)) '(λ (y) (λ (z) z))))
  (check-false (α-equiv? '(λ (x) (λ (y) x)) '(λ (y) (λ (x) x))))
  (check-false (α-equiv? '(λ (x) x) '(λ (y) x)))

  (check-true (α-equiv? 'x 'x))
  (check-false (α-equiv? 'x 'y))

  (check-true (α-equiv? '(f x) '(f x)))
  (check-false (α-equiv? '(f x) '(g x)))
  (check-true (α-equiv? '(λ (f) (f x)) '(λ (g) (g x))))

  (check-true (α-equiv? 'zero 'zero))
  (check-true (α-equiv? '(add1 zero) '(add1 zero)))

  (check-true (α-equiv? ''rugbrød ''rugbrød))
  (check-false (α-equiv? ''rugbrød ''rundstykker))

  (check-true (α-equiv? '(Σ ((half Nat)) (= Nat n (double half)))
                        '(Σ ((blurgh Nat)) (= Nat n (double blurgh)))))
  (check-false (α-equiv? '(Σ ((half Nat)) (= Nat n (double half)))
                         '(Σ ((half Nat)) (= Nat n (twice half)))))

  (check-true (α-equiv? '(the Absurd x) '(the Absurd x)))
  (check-true (α-equiv? '(the Absurd x) '(the Absurd y)))
  (check-true (α-equiv? '(the Absurd x) '(the Absurd (find-the-proof x))))

  (define here (location->srcloc (syntax->location #'here)))
  (define there (location->srcloc (syntax->location #'there)))
  (check-true (α-equiv? `(TODO ,here Nat) `(TODO ,here Nat)))
  (check-false (α-equiv? `(TODO ,here Nat) `(TODO ,there Nat)))

  (check-false (α-equiv? 'zero 'naught))

  (check-true (α-equiv? '(Π ((n Nat)) (= Nat n n)) '(Π ((m Nat)) (= Nat m m))))
  (check-false (α-equiv? '(Π ((n Nat)) (= Nat n n)) '(Π ((m Nat)) (= Nat n n))))
  (check-false (α-equiv? '(Π ((n Nat)) (= Nat n n)) '(Σ ((m Nat)) (= Nat m m))))
  )
