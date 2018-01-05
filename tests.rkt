#lang typed/racket/base

(require racket/match)
(require (except-in typed/rackunit check))
(require "basics.rkt")
(require "typechecker.rkt")

(require/typed "parser.rkt"
  [parse-pie (-> Syntax Src)]
  [parse-pie-decl (-> Syntax (U (List (U 'definition 'claim) Symbol Precise-Loc Src)
                                (List 'check-same Precise-Loc Src Src Src)
                                (List 'expression Src)))])
(require "rep.rkt")





(: foo Symbol)
(define foo 'foo)
(provide foo)

(define-syntax-rule (check-stop-message-equal? e msg-wanted)
  (match e
    [(go _) (error 'not-stop)]
    [(stop _ m)
     (check-equal? m msg-wanted)]))

(check-equal?
 (rep init-ctx
      (parse-pie #'(the (-> Nat Nat)
                (λ (my-var)
                  my-var))))
 (go '(the (Π ((x Nat)) Nat)
           (λ (my-var) my-var))))

(check-equal?
 (rep init-ctx (parse-pie #'(the (-> Nat Nat Nat) (lambda (x x) x))))
 (go '(the (Π ((x Nat)) (Π ((x₁ Nat)) Nat)) (λ (x) (λ (x₁) x₁)))))

(check-equal?
 (rep init-ctx (parse-pie #'(the (-> Nat Nat) (λ (z) z))))
 (go '(the (Π ((x Nat)) Nat) (λ (z) z))))

(check-equal?
 (rep init-ctx (parse-pie #'(which-Nat 1 2 (lambda (x) x))))
 (go '(the Nat zero)))

(check-equal?
 (rep init-ctx (parse-pie #'(which-Nat 0 2 (lambda (x) x))))
 (go '(the Nat (add1 (add1 zero)))))

(check-stop-message-equal? (rep init-ctx (parse-pie #'(the (-> Nat Nat Nat) (lambda (x) x))))
                           '("Expected" (Π ((x₁ Nat)) Nat) "but given" Nat))


(check-stop-message-equal? (rep init-ctx
                                (parse-pie #'(the (-> (-> Nat Nat) Nat)
                                                  (lambda (f x) (f x)))))
                           '("Not a function type:" Nat))

(check-equal? (rep init-ctx (parse-pie #'(the (-> (-> Nat Nat) Nat Nat) (lambda (f x) (f x)))))
              (go '(the (Π ((x (Π ((x Nat)) Nat))) (Π ((x₁ Nat)) Nat)) (λ (f) (λ (x) (f x))))))

(check-equal? (rep init-ctx (parse-pie #'(the (-> Nat (-> Nat Nat) Nat)
                                     (lambda (x f)
                                       (which-Nat 2 x f)))))
              (go
               '(the (Π ((x Nat))
                       (Π ((x₁ (Π ((x₁ Nat))
                                 Nat)))
                         Nat))
                     (λ (x)
                       (λ (f)
                         (f (add1 zero)))))))
(check-equal? (rep init-ctx (parse-pie #'(the (-> Nat (-> Nat Nat) Nat)
                                     (lambda (x f)
                                       (which-Nat x (add1 (add1 zero)) f)))))
              (go
               '(the (Π ((x Nat)) (Π ((x₁ (Π ((x₁ Nat)) Nat))) Nat))
                     (λ (x) (λ (f) (which-Nat x (the Nat (add1 (add1 zero))) (λ (n) (f n))))))))

(check-stop-message-equal? (rep init-ctx (parse-pie #'U))
                           '(U "is a type, but it does not have a type."))

(check-equal? (rep init-ctx (parse-pie #'(the (Pi ((A U)) U) (lambda (B) B))))
              (go '(the (Π ((A U)) U) (λ (B) B))))

(check-equal? (rep init-ctx (parse-pie #'(the (Pi ((A U) (a A)) A) (lambda (B b) b))))
              (go '(the (Π ((A U)) (Π ((a A)) A)) (λ (B) (λ (b) b)))))

(check-equal? (rep init-ctx
                   (parse-pie #'(ind-Nat (add1 (add1 zero))
                                 (lambda (x) Nat)
                                 (add1 zero)
                                 (lambda (n-1 ih)
                                   (add1 ih)))))
              (go '(the Nat (add1 (add1 (add1 zero))))))
(check-equal? (rep init-ctx (parse-pie
                            #'(the (-> Nat Nat Nat)
                                 (lambda (x y)
                                   (ind-Nat x
                                            (lambda (x) Nat)
                                            y
                                            (lambda (n-1 ih)
                                              (add1 ih)))))))
              (go '(the (Π ((x Nat)) (Π ((x₁ Nat)) Nat))
                        (λ (x)
                          (λ (y)
                            (ind-Nat x
                                     (λ (x₁) Nat)
                                     y
                                     (λ (n-1)
                                       (λ (ih)
                                         (add1 ih)))))))))
(check-equal? (rep init-ctx (parse-pie #'(the U (-> Nat Nat))))
              (go '(the U (Π ((x Nat)) Nat))))
(check-stop-message-equal? (rep init-ctx (parse-pie #'(the U (-> U U))))
                           '(U "is a type, but it does not have a type."))
(check-equal? (rep init-ctx (parse-pie #'(-> Nat Nat Nat Nat Nat)))
              (go
               '(the U
                     (Π ((x Nat))
                       (Π ((x₁ Nat))
                         (Π ((x₂ Nat))
                           (Π ((x₃ Nat))
                             Nat)))))))
(check-equal? (rep init-ctx (parse-pie #'(Π ((x Nat) (y Nat)) Nat)))
              (go '(the U (Π ((x Nat)) (Π ((y Nat)) Nat)))))

(check-stop-message-equal? (rep init-ctx (parse-pie #'(the zero zero)))
                           '("Not a type"))
(check-stop-message-equal? (rep init-ctx (parse-pie #'(the (-> Nat U) (lambda (x) x))))
                           '("Expected" U "but given" Nat))
(check-stop-message-equal? (rep init-ctx (parse-pie #'(zero zero)))
                           '("Not a Π:" Nat))
(check-stop-message-equal? (rep init-ctx (parse-pie #'(the (-> Nat U) (lambda (x) x))))
                           '("Expected" U "but given" Nat))
(check-stop-message-equal? (rep init-ctx (parse-pie #'x))
                           '("Unknown variable" x))
(check-equal? (norm-type init-ctx (parse-pie #'Nat))
              (go 'Nat))
(check-stop-message-equal? (norm-type init-ctx (parse-pie #'(Π ((x Nat)) x)))
                           '("Expected" U "but given" Nat))
(check-stop-message-equal? (norm-type init-ctx (parse-pie #'x))
                           '("Unknown variable" x))
(check-equal? (rep init-ctx (parse-pie #''a))
              (go '(the Atom 'a)))
(check-equal? (rep init-ctx (parse-pie #'(the Atom 'a)))
              (go '(the Atom 'a)))
(check-equal? (rep init-ctx (parse-pie #'Atom))
              (go '(the U Atom)))
(check-equal? (rep init-ctx (parse-pie #'(Pair Atom Atom)))
              (go '(the U (Σ ((a Atom)) Atom))))
(check-equal? (rep init-ctx (parse-pie #'(Σ ((x Nat) (y Atom)) Nat)))
              (go '(the U (Σ ((x Nat)) (Σ ((y Atom)) Nat)))))
(check-equal? (rep init-ctx (parse-pie #'(the (Pair Atom Atom) (cons 'olive 'oil))))
              (go '(the (Σ ((x Atom)) Atom) (cons 'olive 'oil))))
(check-equal? (rep init-ctx (parse-pie #'(car (the (Pair Atom Atom) (cons 'olive 'oil)))))
              (go '(the Atom 'olive)))
(check-equal? (rep init-ctx (parse-pie #'(cdr (the (Pair Atom Atom) (cons 'olive 'oil)))))
              (go '(the Atom 'oil)))
(check-equal? (rep init-ctx
                   (parse-pie #'(the (Π ((f (-> Nat U))
                                 (p (Σ ((n Nat))
                                      (f n))))
                               (f (car p)))
                             (λ (f p)
                               (cdr p)))))
              (go
               '(the
                 (Π ((f (Π ((x Nat)) U)))
                   (Π ((p (Σ ((n Nat)) (f n))))
                     (f (car p))))
                 (λ (f) (λ (p) (cdr p))))))
(check-equal? (norm-type init-ctx (parse-pie #'(Σ ((x Nat) (y Nat)) Nat)))
              (go '(Σ ((x Nat)) (Σ ((y Nat)) Nat))))
(check-stop-message-equal? (rep init-ctx (parse-pie #'(car zero)))
                           '("Not a Σ:" Nat))
(check-stop-message-equal? (rep init-ctx (parse-pie #'(cdr zero)))
                           '("Not a Σ:" Nat))
(check-equal? (rep init-ctx (parse-pie #'Trivial))
              (go '(the U Trivial)))
(check-equal? (rep init-ctx (parse-pie #'sole))
              (go '(the Trivial sole)))
(check-equal? (rep init-ctx (parse-pie #'(the (-> Trivial
                                         (Pair Trivial Trivial))
                                     (lambda (x)
                                       (cons x x)))))
              (go
               '(the (Π ((x Trivial))
                       (Σ ((x₁ Trivial)) Trivial))
                     (λ (x)
                       (cons sole sole)))))
(check-equal? (rep init-ctx (parse-pie #'(the (List Atom) nil)))
              (go '(the (List Atom) nil)))
(check-equal? (rep init-ctx (parse-pie #'(the (List Atom) (:: 'foo nil))))
              (go '(the (List Atom) (:: 'foo nil))))
(check-equal? (rep init-ctx (parse-pie #'(ind-List (:: 'lakrids
                                              (:: 'salmiak nil))
                                          (λ (_) Nat)
                                          zero
                                          (lambda (x y z)
                                            (add1 z)))))
              (go '(the Nat (add1 (add1 zero)))))
(check-equal? (rep init-ctx
                   (parse-pie #'(ind-List (:: (add1 (add1 (add1 zero)))
                                      (:: (add1 (add1 zero))
                                          nil))
                                  (λ (_)
                                    Nat)
                                  zero
                                  (lambda (x y z)
                                    (ind-Nat x
                                             (lambda (n)
                                               Nat)
                                             z
                                             (lambda (_ q)
                                               (add1 q)))))))
              (go '(the Nat (add1 (add1 (add1 (add1 (add1 zero))))))))
(check-equal? (rep init-ctx
                   (parse-pie #'(the (-> (List Nat) Nat)
                             (lambda (ns)
                               (ind-List
                                ns
                                (λ (_) Nat)
                                zero
                                (lambda (x y z)
                                  (ind-Nat
                                   x
                                   (lambda (n)
                                     Nat)
                                   z
                                   (lambda (_ q)
                                     (add1 q)))))))))
              (go
               '(the
                 (Π ((x (List Nat)))
                   Nat)
                 (λ (ns)
                   (ind-List
                    ns
                    (λ (_) Nat)
                    zero
                    (λ (x)
                      (λ (y) (λ (z) (ind-Nat x (λ (n) Nat) z (λ (_) (λ (q) (add1 q))))))))))))
(check-stop-message-equal?
 (rep init-ctx (parse-pie #'(the Atom nil)))
 '("nil requires a List type, but was used as a" Atom))
(check-stop-message-equal?
 (rep init-ctx (parse-pie #'(ind-List
                    'brunsviger
                    (λ (_) Nat)
                    zero
                    (lambda (x y z)
                      (ind-Nat x
                               (lambda (n) Nat)
                               z
                               (lambda (_ q) (add1 q)))))))
 '("Not List: " Atom))
(check-equal?
 (rep init-ctx (parse-pie #'(the (Pi ((E U))
                            (-> (List E) (List E)
                                (List E)))
                        (lambda (E)
                          (lambda (xs ys)
                            (rec-List xs
                                      ys
                                      (lambda (h t res)
                                        (:: h res))))))))
 (go
  '(the
    (Π ((E U)) (Π ((x (List E))) (Π ((x₁ (List E))) (List E))))
    (λ (E)
      (λ (xs)
        (λ (ys)
          (rec-List
           xs
           (the (List E) ys)
           (λ (h) (λ (t) (λ (res) (:: h res)))))))))))
(check-equal? (rep init-ctx (parse-pie #'(rec-List (:: 'æbler (:: 'blommer nil))
                                          (:: 'jordbær (:: 'pærer nil))
                                          (lambda (h t res) (:: h res)))))
              (go '(the (List Atom)
                        (:: 'æbler (:: 'blommer (:: 'jordbær (:: 'pærer nil)))))))
(check-stop-message-equal? (rep init-ctx (parse-pie #'(rec-List Nat
                                                       (:: 'jordbær (:: 'pære nil))
                                                       (lambda (h t res)
                                                         (:: h res)))))
                           '("Not List: " U))
(check-equal? (rep init-ctx (parse-pie #'(the (-> Absurd Nat) (lambda (x) (ind-Absurd x Nat)))))
              (go '(the (Π ((x Absurd)) Nat) (λ (x) (ind-Absurd (the Absurd x) Nat)))))
(check-equal? (rep init-ctx (parse-pie #'Absurd))
              (go '(the U Absurd)))
(check-equal? (check-same init-ctx
                          (syntax->location #'here)
                          (parse-pie #'(-> Absurd Absurd Absurd))
                          (parse-pie #'(lambda (x y) x))
                          (parse-pie #'(lambda (x y) y)))
              (go (void)))
(check-stop-message-equal? (check-same init-ctx
                                       (syntax->location #'here)
                                       (parse-pie #'Nat)
                                       (parse-pie #'0)
                                       (parse-pie #'1))
                           '("The expressions" zero "and" (add1 zero) "are not the same" Nat))
(check-equal? (rep init-ctx (parse-pie #'(the (-> Absurd Absurd) (lambda (x) x))))
              (go '(the (Π ((x Absurd)) Absurd) (λ (x) (the Absurd x)))))
(check-equal? (rep init-ctx (parse-pie #'(the (-> Absurd Absurd Absurd) (lambda (x y) x))))
              (go '(the (Π ((x Absurd)) (Π ((x₁ Absurd)) Absurd)) (λ (x) (λ (y) (the Absurd x))))))
(check-stop-message-equal? (rep init-ctx (parse-pie #'(cons 1 2)))
                           '("Can't determine a type"))
(check-equal? (rep init-ctx (parse-pie #'(the (= Nat 0 0) (same 0))))
              (go '(the (= Nat zero zero) (same zero))))
(check-equal? (rep init-ctx (parse-pie #'(the (Pi ((A U)
                                          (a A))
                                         (= A a a))
                                     (lambda (A a)
                                       (same a)))))
              (go '(the (Π ((A U))
                          (Π ((a A))
                            (= A a a)))
                        (λ (A)
                          (λ (a)
                            (same a))))))
(check-equal? (rep init-ctx (parse-pie #'(the (Pi ((x Trivial)
                                          (y Trivial))
                                         (= Trivial x y))
                                     (lambda (x y)
                                       (same sole)))))
              (go '(the (Π ((x Trivial))
                          (Π ((y Trivial))
                            (= Trivial sole sole)))
                        (λ (x)
                          (λ (y)
                            (same sole))))))

(check-equal? (rep init-ctx
                   (parse-pie #'(the (Pi ((x (-> Absurd Trivial))
                                  (y (-> Absurd Trivial)))
                                 (= (-> Absurd Trivial)
                                    x
                                    y))
                             (lambda (f g)
                               (same (lambda (x)
                                       (ind-Absurd x Trivial)))))))
              (go
               '(the
                 (Π ((x (Π ((x Absurd)) Trivial)))
                   (Π ((y (Π ((x₁ Absurd)) Trivial)))
                     (= (Π ((x₁ Absurd)) Trivial)
                        (λ (x₁) sole)
                        (λ (x₁) sole))))
                 (λ (f)
                   (λ (g)
                     (same (λ (x) sole)))))))
(check-equal? (rep init-ctx (parse-pie #'(the (Pi ((x (-> Trivial Absurd)) (y (-> Trivial Absurd))) (= (-> Trivial Absurd) x y)) (lambda (f g) (ind-Absurd (f sole) (= (-> Trivial Absurd) f g))))))
              (go
               '(the
                 (Π ((x (Π ((x Trivial)) Absurd)))
                   (Π ((y (Π ((x₁ Trivial)) Absurd)))
                     (= (Π ((x₁ Trivial)) Absurd)
                        (λ (x₁) (the Absurd (x sole)))
                        (λ (x₁) (the Absurd (y sole))))))
                 (λ (f)
                   (λ (g)
                     (ind-Absurd
                      (the Absurd (f sole))
                      (= (Π ((x Trivial)) Absurd)
                         (λ (x) (the Absurd (f sole)))
                         (λ (x) (the Absurd (g sole))))))))))

(check-equal? (rep init-ctx (parse-pie #'(the (Pi ((x (-> Trivial Absurd))
                                          (y (-> Trivial Absurd)))
                                                 (= Absurd
                                                    (the Absurd (x sole))
                                                    (the Absurd (y sole))))
                                     (lambda (f g)
                                       (same (f sole))))))
              (go
               '(the (Π ((x (Π ((x Trivial))
                              Absurd)))
                       (Π ((y (Π ((x₁ Trivial))
                                Absurd)))
                         (= Absurd
                            (the Absurd (x sole))
                            (the Absurd (y sole)))))
                     (λ (f)
                       (λ (g)
                         (same (the Absurd (f sole))))))))
(check-equal? (rep init-ctx
                   (parse-pie #'(the (Pi ((x (-> Trivial Absurd))
                                  (y (-> Trivial Absurd)))
                                 (= (-> Trivial Absurd) x y))
                             (lambda (f g)
                               (same f)))))
              (go
               '(the
                 (Π ((x (Π ((x Trivial)) Absurd)))
                   (Π ((y (Π ((x₁ Trivial)) Absurd)))
                     (= (Π ((x₁ Trivial)) Absurd)
                        (λ (x₁) (the Absurd (x sole)))
                        (λ (x₁) (the Absurd (y sole))))))
                 (λ (f)
                   (λ (g)
                     (same (λ (x₁) (the Absurd (f sole)))))))))

(check-equal? (rep init-ctx (parse-pie #'(the (Pi ((n Nat)
                                          (m Nat))
                                         (-> (= Nat n m)
                                             (= Nat m n)))
                                     (lambda (n m n=m)
                                       (replace n=m
                                                (lambda (k)
                                                  (= Nat k n))
                                                (same n))))))
              (go
               '(the (Π ((n Nat))
                       (Π ((m Nat))
                         (Π ((x (= Nat n m)))
                           (= Nat m n))))
                     (λ (n)
                       (λ (m)
                         (λ (n=m)
                           (replace n=m
                                    (λ (k)
                                      (= Nat k n))
                                    (same n))))))))

(check-equal? (rep init-ctx (parse-pie #'(replace (the (= Nat 4 4) (same 4))
                                         (lambda (k)
                                           (= Nat k 4))
                                         (same 4))))
              (go
               '(the (= Nat
                        (add1 (add1 (add1 (add1 zero))))
                        (add1 (add1 (add1 (add1 zero)))))
                     (same (add1 (add1 (add1 (add1 zero))))))))

(check-stop-message-equal?
 (rep init-ctx (parse-pie #'(replace 4 5 6)))
 '("Expected an expression with = type, but the type was" Nat))
(check-stop-message-equal?
 (rep init-ctx (parse-pie #'(the Nat (same 3))))
 '("same requires an = type, but was used as a" Nat))

(check-equal?
 (rep init-ctx (parse-pie #'(the (Vec Atom 3)
                        (vec:: 'råkost
                               (vec:: 'rødbeder
                                      (vec:: 'grønkål
                                             vecnil))))))
 (go
  '(the (Vec Atom (add1 (add1 (add1 zero))))
        (vec:: 'råkost
               (vec:: 'rødbeder
                      (vec:: 'grønkål
                             vecnil))))))

(check-equal?
 (rep init-ctx (parse-pie #'(head (the (Vec Atom 1) (vec:: 'rosenkål vecnil)))))
 (go '(the Atom 'rosenkål)))
(check-equal?
 (rep init-ctx (parse-pie #'(tail (the (Vec Atom 1) (vec:: 'rosenkål vecnil)))))
 (go '(the (Vec Atom zero) vecnil)))
(check-equal?
 (rep init-ctx (parse-pie #'(the (Pi ((A U) (len Nat)) (-> (Vec A (add1 len)) (Vec A (add1 len)))) (lambda (A len) (lambda (xs) (vec:: (head xs) (tail xs)))))))
 (go
  '(the
    (Π ((A U))
      (Π ((len Nat))
        (Π ((x (Vec A (add1 len))))
          (Vec A (add1 len)))))
    (λ (A)
      (λ (len)
        (λ (xs)
          (vec:: (head xs)
                 (tail xs))))))))
(check-stop-message-equal?
 (rep init-ctx (parse-pie #'(the (Vec Atom 2) vecnil)))
 '(vecnil "requires that the length be zero, not" (add1 (add1 zero))))

(check-stop-message-equal?
 (rep init-ctx (parse-pie #'(the Nat vecnil)))
 '(vecnil "must be a Vec, but was used in a" Nat "context."))

(check-stop-message-equal?
 (rep init-ctx (parse-pie #'(the (Pi ((k Nat)) (Vec Atom k)) (lambda (k) (vec:: 'hey vecnil)))))
 '("vec:: requires that the length have add1 on top, not" k))
(check-stop-message-equal?
 (rep init-ctx (parse-pie #'(the (Vec Atom 0) (vec:: 'øllebrød vecnil))))
 '("vec:: requires that the length have add1 on top, not" zero))
(check-stop-message-equal?
 (rep init-ctx (parse-pie #'(the Nat (vec:: 3 2))))
 '("vec:: must be a Vec, but was used in a" Nat "context."))
(check-equal?
 (rep init-ctx (parse-pie #'(Vec Nat 2)))
 (go '(the U (Vec Nat (add1 (add1 zero))))))
(check-stop-message-equal?
 (rep init-ctx (parse-pie #'(head (the (Vec Atom 0) vecnil))))
 '("Expected a Vec with add1 at the top of the length, got" zero))
(check-stop-message-equal?
 (rep init-ctx (parse-pie #'(head zero)))
 '("Expected a Vec, got" Nat))
(check-stop-message-equal?
 (rep init-ctx (parse-pie #'(tail (the (Vec Atom 0) vecnil))))
 '("Expected a Vec with add1 at the top of the length, got" zero))
(check-stop-message-equal?
 (rep init-ctx (parse-pie #'(tail zero)))
 '("Expected a Vec, got" Nat))
(check-equal? (rep init-ctx (parse-pie #'(ind-Vec 0
                                         (the (Vec Nat 0) vecnil)
                                         (lambda (k xs) Nat)
                                         0
                                         (lambda (k e es ih)
                                           (add1 ih)))))
              (go '(the Nat zero)))
(check-equal? (rep init-ctx (parse-pie
                            #'(ind-Vec 2
                                     (the (Vec Nat 2)
                                          (vec:: 1
                                                 (vec:: 3
                                                        vecnil)))
                                     (lambda (k xs) Nat)
                                     0
                                     (lambda (k e es ih)
                                       (add1 ih)))))
              (go '(the Nat (add1 (add1 zero)))))
(check-equal? (rep init-ctx
                   (parse-pie
                    #'(the (Pi ((k Nat) (xs (Vec Nat k))) Nat)
                         (lambda (k xs)
                           (ind-Vec k
                                    xs
                                    (lambda (k xs)
                                      Nat)
                                    0
                                    (lambda (k e es ih)
                                      (add1 ih)))))))
              (go
               '(the
                 (Π ((k Nat)) (Π ((xs (Vec Nat k))) Nat))
                 (λ (k)
                   (λ (xs)
                     (ind-Vec k
                              xs
                              (λ (k₁) (λ (xs₁) Nat))
                              zero
                              (λ (k₁)
                                (λ (e)
                                  (λ (es)
                                    (λ (ih)
                                      (add1 ih)))))))))))
(check-equal? (rep init-ctx
                   (parse-pie #'(the (Either Nat Atom) (left 4))))
              (go '(the (Either Nat Atom) (left (add1 (add1 (add1 (add1 zero))))))))
(check-equal? (rep init-ctx
                   (parse-pie #'(the (Either Nat Atom) (right 'løgsuppe))))
              (go '(the (Either Nat Atom) (right 'løgsuppe))))
(check-equal? (rep init-ctx (parse-pie #'(Either Nat Atom)))
              (go '(the U (Either Nat Atom))))
(check-equal? (rep init-ctx (parse-pie #'(the (-> (Either Nat Atom) (Either Atom Nat))
                                     (lambda (x)
                                       (ind-Either x
                                                   (lambda (x) (Either Atom Nat))
                                                   (lambda (x) (right x))
                                                   (lambda (x) (left x)))))))
              (go
               '(the (Π ((x (Either Nat Atom))) (Either Atom Nat))
                     (λ (x)
                       (ind-Either
                        x
                        (λ (x₁) (Either Atom Nat))
                        (λ (x₁) (right x₁))
                        (λ (x₁) (left x₁)))))))

(check-equal? (rep init-ctx (parse-pie
                            #'(the (-> (Vec Nat 2) Nat)
                                 (lambda (xs)
                                   (ind-Vec 2
                                            xs
                                            (lambda (k xs)
                                              Nat)
                                            0
                                            (lambda (k x xs ih)
                                              (add1 ih)))))))
              (go
               '(the (Π ((x (Vec Nat (add1 (add1 zero)))))
                       Nat)
                     (λ (xs)
                       (ind-Vec
                        (add1 (add1 zero))
                        xs
                        (λ (k)
                          (λ (xs₁) Nat))
                        zero
                        (λ (k)
                          (λ (x)
                            (λ (xs₁)
                              (λ (ih)
                                (add1 ih))))))))))
(check-equal? (rep init-ctx
                   (parse-pie #'(the (Pi ((n Nat)) (-> (Vec Nat n) Nat))
                             (lambda (n xs)
                               (ind-Vec n
                                        xs
                                        (lambda (k xs) Nat)
                                        0
                                        (lambda (k x xs ih) (add1 ih)))))))
              (go
               '(the
                 (Π ((n Nat)) (Π ((x (Vec Nat n))) Nat))
                 (λ (n)
                   (λ (xs)
                     (ind-Vec
                      n
                      xs
                      (λ (k) (λ (xs₁) Nat))
                      zero
                      (λ (k)
                        (λ (x)
                          (λ (xs₁)
                            (λ (ih)
                              (add1 ih)))))))))))
(check-equal? (rep init-ctx (parse-pie #'(symm (the (= Nat 2 2) (same 2)))))
              (go
               '(the
                 (= Nat (add1 (add1 zero)) (add1 (add1 zero)))
                 (same (add1 (add1 zero))))))

(check-equal? (rep init-ctx (parse-pie #'(the (-> (= Nat 2 5) (= Nat 5 2)) (lambda (x) (symm x)))))
              (go
               '(the
                 (Π ((x (= Nat
                           (add1 (add1 zero))
                           (add1 (add1 (add1 (add1 (add1 zero))))))))
                   (= Nat
                      (add1 (add1 (add1 (add1 (add1 zero)))))
                      (add1 (add1 zero))))
                 (λ (x)
                   (symm x)))))
(check-equal? (rep init-ctx (parse-pie #'(the (-> (= Nat 2 5) (= Nat 5 3) (= Nat 2 3))
                                     (lambda (x y) (trans x y)))))
              (go
               '(the (Π ((x (= Nat (add1 (add1 zero)) (add1 (add1 (add1 (add1 (add1 zero))))))))
                       (Π ((x₁ (= Nat
                                  (add1 (add1 (add1 (add1 (add1 zero)))))
                                  (add1 (add1 (add1 zero))))))
                         (= Nat (add1 (add1 zero)) (add1 (add1 (add1 zero))))))
                     (λ (x) (λ (y) (trans x y))))))
(check-equal? (rep init-ctx (parse-pie #'(the (-> (= Nat 5 3) (= Nat 5 3)) (lambda (y) (trans (the (= Nat 5 5) (same 5)) y)))))
              (go
               '(the
                 (Π ((x (=
                         Nat
                         (add1 (add1 (add1 (add1 (add1 zero)))))
                         (add1 (add1 (add1 zero))))))
                   (= Nat (add1 (add1 (add1 (add1 (add1 zero))))) (add1 (add1 (add1 zero)))))
                 (λ (y)
                   (trans (same (add1 (add1 (add1 (add1 (add1 zero))))))
                          y)))))
(check-equal? (rep init-ctx
                   (parse-pie #'(the (-> (= Nat 5 3)
                                 (= Nat 5 3))
                             (lambda (y)
                               (trans y (the (= Nat 3 3) (same 3)))))))
              (go
               '(the
                 (Π ((x (= Nat
                           (add1 (add1 (add1 (add1 (add1 zero)))))
                           (add1 (add1 (add1 zero))))))
                   (= Nat (add1 (add1 (add1 (add1 (add1 zero))))) (add1 (add1 (add1 zero)))))
                 (λ (y)
                   (trans y (same (add1 (add1 (add1 zero)))))))))
(check-equal? (rep init-ctx (parse-pie #'(trans (the (= Nat 5 5) (same 5)) (the (= Nat 5 5) (same 5)))))
              (go
               '(the
                 (= Nat
                    (add1 (add1 (add1 (add1 (add1 zero)))))
                    (add1 (add1 (add1 (add1 (add1 zero))))))
                 (same (add1 (add1 (add1 (add1 (add1 zero)))))))))
(check-equal? (rep init-ctx (parse-pie #'(iter-Nat 2
                                          3
                                          (λ (ih)
                                            (add1 ih)))))
              (go '(the Nat (add1 (add1 (add1 (add1 (add1 zero))))))))
(check-equal? (rep init-ctx
                   (parse-pie #'(the (-> Nat Nat
                                 Nat)
                             (lambda (x y)
                               (iter-Nat x
                                         y
                                         (λ (n-1)
                                           (add1 n-1)))))))
              (go
               '(the
                 (Π ((x Nat))
                   (Π ((x₁ Nat))
                     Nat))
                 (λ (x)
                   (λ (y)
                     (iter-Nat x
                               (the Nat y)
                               (λ (n-1)
                                 (add1 n-1))))))))
(check-equal? (rep init-ctx
                   (parse-pie #'(the (-> Nat Nat Nat)
                             (lambda (x y)
                               (rec-Nat x
                                        y
                                        (λ (n-1 ih)
                                          (add1 ih)))))))
              (go
               '(the
                 (Π ((x Nat))
                   (Π ((x₁ Nat))
                     Nat))
                 (λ (x)
                   (λ (y)
                     (rec-Nat x
                              (the Nat y)
                              (λ (n-1)
                                (λ (ih)
                                  (add1 ih)))))))))

(check-equal? (rep init-ctx (parse-pie #'(rec-Nat 2 3 (λ (n-1 ih) (add1 ih)))))
              (go '(the Nat (add1 (add1 (add1 (add1 (add1 zero))))))))

(check-equal? (for/fold ([st init-ctx])
                        ([d (map parse-pie-decl
                                 (list #'(claim four
                                                Nat)
                                       #'(define four
                                           4)
                                       #'(claim eight
                                                Nat)
                                       #'(define eight
                                           (add1 (add1 (add1 (add1 four)))))))])
                (match d
                  [`(claim ,x ,loc ,t)
                   (match (add-claim st x loc t)
                     [(go new-st) new-st]
                     [(stop where msg)
                      (error (format "Nope: ~a" msg))])]
                  [`(definition ,x ,loc ,v)
                   (match (add-def st x loc v)
                     [(go new-st) new-st]
                     [(stop where msg)
                      (error (format "Nope: ~a" msg))])]))
              (list
               (cons 'eight
                     (def
                       'NAT
                       (ADD1 (ADD1 (ADD1 (ADD1 (ADD1 (ADD1 (ADD1 (ADD1 'ZERO))))))))))
               (cons 'four
                     (def
                       'NAT
                       (ADD1 (ADD1 (ADD1 (ADD1 'ZERO))))))))


(check-equal?
 (rep init-ctx
     (parse-pie #'((the (Pi ((A U) (B U))
                    (-> (Either A B)
                        (Either B A)))
                (lambda (A B e)
                  (ind-Either e
                              (lambda (_) (Either B A))
                              (lambda (x) (right x))
                              (lambda (x) (left x)))))
           Nat Trivial (left 2))))
 (go '(the (Either Trivial Nat) (right (add1 (add1 zero))))))

(check-equal?
 (rep init-ctx
     (parse-pie #'((the (Pi ((A U) (B U))
                    (-> (Either A B)
                        (Either B A)))
                (lambda (A B e)
                  (ind-Either e
                              (lambda (_) (Either B A))
                              (lambda (x) (right x))
                              (lambda (x) (left x)))))
           Nat)))
 (go
 '(the
   (Π ((B U)) (Π ((x (Either Nat B))) (Either B Nat)))
   (λ (B)
     (λ (e)
       (ind-Either
        e
        (λ (_) (Either B Nat))
        (λ (x) (right x))
        (λ (x) (left x))))))))

(check-equal? (rep init-ctx (parse-pie #'(cong (the (= Nat 2 2) (same 2))
                                      (the (-> Nat Nat) (lambda (x) (add1 x))))))
              (go
               '(the (= Nat (add1 (add1 (add1 zero))) (add1 (add1 (add1 zero))))
                     (same (add1 (add1 (add1 zero)))))))

(check-equal? (rep init-ctx (parse-pie #'(the (Pi ((x Nat)
                                          (y Nat)
                                          (p (= Nat x y))
                                          (f (-> Nat (List Atom))))
                                         (= (List Atom) (f x) (f y)))
                                     (lambda (x y p f)
                                       (cong p f)))))
              (go '(the (Π ((x Nat))
                          (Π ((y Nat))
                            (Π ((p (= Nat x y)))
                              (Π ((f (Π ((x₁ Nat)) (List Atom)))) (= (List Atom) (f x) (f y))))))
                        (λ (x) (λ (y) (λ (p) (λ (f) (cong p (List Atom) (λ (x₁) (f x₁))))))))))

(check-equal? (rep init-ctx (parse-pie #'(the (Pi ((A U)
                                                   (x A)
                                                   (y A)
                                                   (p1 (= A x y))
                                                   (z A)
                                                   (p2 (= A y z)))
                                                  (= A x z))
                                              (λ (A x y p1)
                                                (ind-= p1
                                                       (λ (w)
                                                         (λ (p)
                                                           (Pi ((z A))
                                                               (-> (= A w z)
                                                                   (= A x z)))))
                                                       (λ (z eq2)
                                                         eq2))))))
              (go
               '(the
                 (Π
                     ((A U))
                   (Π
                       ((x A))
                     (Π
                         ((y A))
                       (Π ((p1 (= A x y))) (Π ((z A)) (Π ((p2 (= A y z))) (= A x z)))))))
                 (λ (A)
                   (λ (x)
                     (λ (y)
                       (λ (p1)
                         (λ (z)
                           (λ (p2)
                             (((ind-=
                                p1
                                (λ (w) (λ (p) (Π ((z₁ A)) (Π ((x₁ (= A w z₁))) (= A x z₁)))))                                (λ (z₁) (λ (eq2) eq2)))
                               z)
                              p2))))))))))

(check-stop-message-equal?  (rep init-ctx (parse-pie #'(the (Pi ((A U)
                                                                 (x A)
                                                                 (y A)
                                                                 (p1 (= A x y))
                                                                 (z A)
                                                                 (p2 (= A y z)))
                                                                (= A x z))
                                                            (λ (A x y p1)
                                                              (ind-= p1
                                                                     (λ (w)
                                                                       (λ (p)
                                                                         (Pi ((z A))
                                                                             (-> (= A x z)
                                                                                 (= A w z)))))
                                                                     (λ (z eq2)
                                                                       eq2))))))
                            '("Expected"
                              (Π ((z A)) (Π ((p2 (= A y z))) (= A x z)))
                              "but given"
                              (Π ((z A)) (Π ((x₁ (= A x z))) (= A y z)))))

(check-stop-message-equal? (rep init-ctx (parse-pie #'(the (Pi ((A U)
                                                                (x A)
                                                                (y A)
                                                                (p1 (= A x y))
                                                                (z A)
                                                                (p2 (= A y z)))
                                                               (= A x z))
                                                           (λ (A x y p1)
                                                             (ind-= 33
                                                                    (λ (w)
                                                                      (λ (p)
                                                                        (Pi ((z A))
                                                                            (-> (= A x z)
                                                                                (= A w z)))))
                                                                    (λ (z eq2)
                                                                      eq2))))))
                           '("Expected evidence of equality, got " Nat))
