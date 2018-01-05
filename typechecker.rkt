#lang typed/racket/base

;;; typechecker.rkt
;;;
;;; This file implements type checking of expressions and definitions.

(require "basics.rkt" "normalize.rkt" "alpha.rkt")
(require racket/match (for-syntax racket/base syntax/parse))
(provide (all-defined-out))


(require/typed "locations.rkt"
  [location-for-info? (-> Loc Boolean)]
  [location->srcloc (-> Loc Srcloc)]
  [not-for-info (-> Loc Precise-Loc)])

(: pie-info-hook (Parameterof (-> Loc
                                  (U 'definition
                                     (List 'binding-site Core)
                                     (List 'is-type Core)
                                     (List 'has-type Core)
                                     (List 'TODO Serializable-Ctx Core))
                                  Void)))
(define pie-info-hook
  (make-parameter (lambda (where what) (void))))

(: send-pie-info (-> Loc
                     (U 'definition
                        (List 'binding-site Core)
                        (List 'is-type Core)
                        (List 'has-type Core)
                        (List 'TODO Serializable-Ctx Core))
                     Void))
(define (send-pie-info where what)
  (when (location-for-info? where)
    ((pie-info-hook) where what)))

(: is-type (-> Ctx Src (Perhaps Core)))
(define (is-type Γ in)
  (: the-type (Perhaps Core))
  (define the-type
   (match (src-stx in)
     ['U (go 'U)]
     ['Nat (go 'Nat)]
     [`(-> ,A ,B)
      (let ([x (fresh Γ 'x)])
        (go-on ([A-out (is-type Γ A)]
                [B-out (is-type (bind-free Γ
                                            x
                                            (val-in-ctx Γ A-out))
                                B)])
          (go `(Π ((,x ,A-out)) ,B-out))))]
     [`(-> ,A ,B ,C . ,C*)
      (let ([x (fresh Γ 'x)])
        (go-on ([A-out (is-type Γ A)]
                [t-out (is-type (bind-free Γ x (val-in-ctx Γ A-out))
                                (@ (src-loc in)
                                   `(-> ,B ,C . ,C*)))])
          (go `(Π ((,x ,A-out)) ,t-out))))]
     [`(Π ((,(binder x-loc x) ,A)) ,B)
      (let ((y (fresh Γ x)))
        (go-on ([A-out (is-type Γ A)]
                [A-outv (go (val-in-ctx Γ A-out))]
                [B-out (is-type (bind-free Γ y A-outv) B)])
          (begin ((pie-info-hook) x-loc `(binding-site ,A-out))
                 (go `(Π ((,y ,A-out)) ,B-out)))))]
     [`(Π ((,(binder x-loc x) ,A) (,y ,A1) . ,more) ,B)
      (let ((z (fresh Γ x)))
        (go-on ([A-out (is-type Γ A)]
                [A-outv (go (val-in-ctx Γ A-out))]
                [B-out (is-type (bind-free Γ z A-outv)
                                (@ (src-loc in)
                                   `(Π ,(list* `(,y ,A1) more) ,B)))])
          (begin ((pie-info-hook) x-loc `(binding-site ,A-out))
                 (go `(Π ((,z ,A-out)) ,B-out)))))]
     ['Atom
      (go 'Atom)]
     [`(Pair ,A ,D)
      (let ([x (fresh Γ 'x)])
        (go-on ([A-out (is-type Γ A)]
                [D-out (is-type (bind-free Γ x (val-in-ctx Γ A-out))
                                D)])
          (go `(Σ ((,x ,A-out)) ,D-out))))]
     [`(Σ ((,(binder x-loc x) ,A)) ,D)
      (let ((y (fresh Γ x)))
        (go-on ([A-out (is-type Γ A)]
                [A-outv (go (val-in-ctx Γ A-out))]
                [D-out (is-type (bind-free Γ y A-outv)
                                D)])
          (begin ((pie-info-hook) x-loc `(binding-site ,A-out))
                 (go `(Σ ((,y ,A-out)) ,D-out)))))]
     [`(Σ ((,(binder x-loc x) ,A) (,y ,A1) . ,more) ,D)
      (let ((z (fresh Γ x)))
        (go-on ([A-out (is-type Γ A)]
                [A-outv (go (val-in-ctx Γ A-out))]
                [D-out (is-type (bind-free Γ z A-outv)
                                (@ (src-loc in)
                                   `(Σ ,(list* `(,y ,A1) more) ,D)))])
          (begin ((pie-info-hook) x-loc `(binding-site ,A-out))
                 (go `(Σ ((,z ,A-out)) ,D-out)))))]
     ['Trivial (go 'Trivial)]
     [`(LiΓ ,E)
      (go-on ((E-out (is-type Γ E)))
        (go `(List ,E-out)))]
     ['Absurd (go 'Absurd)]
     [`(= ,A ,from ,to)
      (go-on ((A-out (is-type Γ A))
              (Av (go (val-in-ctx Γ A-out)))
              (from-out (check Γ from Av))
              (to-out (check Γ to Av)))
        (go `(= ,A-out ,from-out ,to-out)))]
     [`(Vec ,E ,len)
      (go-on ((E-out (is-type Γ E))
              (len-out (check Γ len 'NAT)))
        (go `(Vec ,E-out ,len-out)))]
     [`(Either ,L ,R)
      (go-on ((L-out (is-type Γ L))
              (R-out (is-type Γ R)))
        (go `(Either ,L-out ,R-out)))]
     [other
      (match (check Γ (@ (src-loc in) other) 'UNIVERSE)
        [(go t-out)
         (go t-out)]
        [(stop where why)
         (cond
           [(and (symbol? other) (var-name? other))
            (go-on ((other-tv (var-type Γ (src-loc in) other)))
              (stop (src-loc in)
                    `("Expected" U
                                 "but given"
                                 ,(read-back-type Γ other-tv))))]
           [else
            (stop (src-loc in) `("Not a type"))])])]))
  (go-on ((t the-type))
    (begin (send-pie-info (src-loc in) `(is-type ,t))
           (go t))))

(: synth (-> Ctx Src (Perhaps (List 'the Core Core))))
(define (synth Γ e)
  (: the-expr (Perhaps (List 'the Core Core)))
  (define the-expr
   (match (src-stx e)
     ['Nat (go `(the U Nat))]
     ['U (stop (src-loc e)
               `(U
                 "is a type, but it does not have a type."))]
     [`(-> ,A ,B)
      (let ([z (fresh Γ 'x)])
        (go-on ([A-out (check Γ A 'UNIVERSE)]
                [B-out (check (bind-free Γ z (val-in-ctx Γ A-out))
                              B
                              'UNIVERSE)])
          (go `(the U (Π ((,z ,A-out)) ,B-out)))))]
     [`(-> ,A ,B ,C . ,C*)
      (let ([z (fresh Γ 'x)])
        (go-on ([A-out (check Γ A 'UNIVERSE)]
                [t-out (check (bind-free Γ z (val-in-ctx Γ A-out))
                              (@ (not-for-info (src-loc e))
                                 `(-> ,B ,C . ,C*))
                              'UNIVERSE)])
          (go `(the U (Π ((,z ,A-out)) ,t-out)))))]
     [`(Π ((,(binder x-loc x) ,A)) ,B)
      (go-on ([A-out (check Γ A 'UNIVERSE)]
              [B-out (check (bind-free Γ x
                                        (val-in-ctx Γ A-out))
                            B
                            'UNIVERSE)])
        (begin ((pie-info-hook) x-loc `(binding-site ,A-out))
               (go `(the U (Π ((,x ,A-out)) ,B-out)))))]
     [`(Π ((,(binder x-loc x) ,A) (,y ,A1) . ,more) ,B)
      (go-on ([A-out (check Γ A 'UNIVERSE)]
              [B-out (check (bind-free Γ x (val-in-ctx Γ A-out))
                            (@ (not-for-info (src-loc e))
                               `(Π ,(list* `(,y ,A1) more) ,B))
                            'UNIVERSE)])
        (begin ((pie-info-hook) x-loc `(binding-site ,A-out))
               (go `(the U (Π ((,x ,A-out)) ,B-out)))))]
     ['zero (go `(the Nat zero))]
     [`(add1 ,n)
      (go-on ((n-out (check Γ n 'NAT)))
        (go `(the Nat (add1 ,n-out))))]
     [`(which-Nat ,tgt ,b ,s)
      (go-on ((tgt-out (check Γ tgt 'NAT))
              (`(the ,b-t-out ,b-out)
               (synth Γ b))
              (s-out
               (check Γ
                      s
                      (let ([n-1 (fresh Γ 'n-1)])
                        (PI n-1 'NAT (FO-CLOS (ctx->env Γ) n-1 b-t-out))))))
        (go `(the ,b-t-out
                  (which-Nat ,tgt-out (the ,b-t-out ,b-out) ,s-out))))]
     [`(iter-Nat ,tgt ,b ,s)
      (go-on ((tgt-out (check Γ tgt 'NAT))
              (`(the ,b-t-out ,b-out)
               (synth Γ b))
              (s-out
               (check Γ
                      s
                      (let ([old (fresh Γ 'old)])
                        (val-in-ctx Γ `(Π ((,old ,b-t-out))
                                         ,b-t-out))))))
        (go `(the ,b-t-out
                  (iter-Nat ,tgt-out (the ,b-t-out ,b-out) ,s-out))))]
     [`(rec-Nat ,tgt ,b ,s)
      (go-on ((tgt-out (check Γ tgt 'NAT))
              (`(the ,b-t-out ,b-out)
               (synth Γ b))
              (s-out
               (check Γ
                      s
                      (let ([n-1 (fresh Γ 'n-1)]
                            [old (fresh Γ 'old)])
                        (val-in-ctx Γ `(Π ((,n-1 Nat))
                                      (Π ((,old ,b-t-out))
                                        ,b-t-out)))))))
        (go `(the ,b-t-out
                  (rec-Nat ,tgt-out (the ,b-t-out ,b-out) ,s-out))))]
     [`(ind-Nat ,tgt ,mot ,b ,s)
      (go-on ((tgt-out (check Γ tgt 'NAT))
              (mot-out (check Γ mot (PI 'n 'NAT (HO-CLOS (lambda (n) 'UNIVERSE)))))
              (mot-val (go (val-in-ctx Γ mot-out)))
              (b-out (check Γ b (do-ap mot-val 'ZERO)))
              (s-out (check
                      Γ
                      s
                      (Π-type ((n-1 'NAT)
                               (ih (do-ap mot-val n-1)))
                              (do-ap mot-val (ADD1 n-1))))))
        (go `(the (,mot-out ,tgt-out)
                  (ind-Nat ,tgt-out ,mot-out ,b-out ,s-out))))]
     ['Atom (go `(the U Atom))]
     [`(Pair ,A ,D)
      (let ([a (fresh Γ 'a)])
        (go-on ([A-out (check Γ A 'UNIVERSE)]
                [D-out (check (bind-free Γ a (val-in-ctx Γ A-out))
                              D
                              'UNIVERSE)])
          (go `(the U (Σ ((,a ,A-out)) ,D-out)))))]
     [`(Σ ((,(binder x-loc x) ,A)) ,D)
      (go-on ([A-out (check Γ A 'UNIVERSE)]
              [D-out (check (bind-free Γ
                                        x
                                        (val-in-ctx Γ A-out))
                            D
                            'UNIVERSE)])
        (begin ((pie-info-hook) x-loc `(binding-site ,A-out))
               (go `(the U (Σ ((,x ,A-out)) ,D-out)))))]
     [`(Σ ((,(binder x-loc x) ,A) (,y ,A1) . ,more) ,D)
      (go-on ([A-out (check Γ A 'UNIVERSE)]
              [D-out (check (bind-free Γ x (val-in-ctx Γ A-out))
                            (@ (not-for-info (src-loc e))
                               `(Σ ,(list* `(,y ,A1) more) ,D))
                            'UNIVERSE)])
        (begin ((pie-info-hook) x-loc `(binding-site ,A-out))
               (go `(the U (Σ ((,x ,A-out)) ,D-out)))))]
     [`(car ,p)
      (go-on ([`(the ,p-t ,p-out) (synth Γ p)])
        (match (val-in-ctx Γ p-t)
          [(SIGMA x A clos)
           (go `(the ,(read-back-type Γ A) (car ,p-out)))]
          [non-Sigma
           (stop (src-loc e)
                 `("Not a Σ:" ,(read-back-type Γ non-Sigma)))]))]
     [`(cdr ,p)
      (go-on ([`(the ,p-t ,p-out) (synth Γ p)])
        (match (val-in-ctx Γ p-t)
          [(SIGMA x A c)
           (go `(the ,(read-back-type Γ
                                      (val-of-closure c (do-car (val-in-ctx Γ p-out))))
                     (cdr ,p-out)))]
          [non-Sigma
           (stop (src-loc e)
                 `("Not a Σ:" ,(read-back-type Γ non-Sigma)))]))]
     [`(quote ,a)
      (if (atom-ok? a)
          (go `(the Atom (quote ,a)))
          (stop (src-loc e) `("Atoms consist of letters and hyphens.")))]
     ['Trivial
      (go `(the U Trivial))]
     ['sole
      (go `(the Trivial sole))]
     [`(ind-List ,tgt ,mot ,b ,s)
      (go-on ((`(the ,tgt-t ,tgt-out) (synth Γ tgt)))
        (match (val-in-ctx Γ tgt-t)
          [(LIST E)
           (go-on ((mot-out (check
                             Γ
                             mot
                             (PI 'xs (LIST E) (FO-CLOS (ctx->env Γ) 'xs 'U))))
                   (mot-val (go (val-in-ctx Γ mot-out)))
                   (b-out (check Γ b (do-ap mot-val 'NIL)))
                   (s-out
                    (check Γ
                           s
                           (Π-type ((e E)
                                    (es (LIST E))
                                    (ih (do-ap mot-val es)))
                                   (do-ap mot-val (LIST:: e es))))))
             (go `(the (,mot-out ,tgt-out)
                       (ind-List ,tgt-out
                                 ,mot-out
                                 ,b-out
                                 ,s-out))))]
          [other (stop (src-loc e)
                       `("Not List: "
                         ,(read-back-type Γ other)))]))]
     [`(rec-List ,tgt ,b ,s)
      (go-on ((`(the ,tgt-t ,tgt-out) (synth Γ tgt)))
        (match (val-in-ctx Γ tgt-t)
          [(LIST E)
           (go-on ((`(the ,b-t-out ,b-out) (synth Γ b))
                   (b-t-val (go (val-in-ctx Γ b-t-out)))
                   (s-out (let ([x (fresh Γ 'x)]
                                [xs (fresh Γ 'xs)]
                                [ih (fresh Γ 'ih)])
                            (check
                             Γ
                             s
                             (Π-type ((e E)
                                      (es (LIST E))
                                      (ih b-t-val))
                                     b-t-val)))))
             (go `(the ,b-t-out
                       (rec-List ,tgt-out
                                 (the ,b-t-out ,b-out)
                                 ,s-out))))]
          [other (stop (src-loc e)
                       `("Not List: "
                         ,(read-back-type Γ other)))]))]
     [`(List ,E)
      (go-on ((E-out (check Γ E 'UNIVERSE)))
        (go `(the U (List ,E-out))))]
     [`(:: ,e ,es)
      (go-on ((`(the ,E ,e-out) (synth Γ e))
              (es-out (check Γ es (val-in-ctx Γ `(List ,E)))))
        (go `(the (List ,E) (:: ,e-out ,es-out))))]
     ['Absurd
      (go `(the U Absurd))]
     [`(ind-Absurd ,tgt ,mot)
      (go-on ((tgt-out (check Γ tgt 'ABSURD))
              (mot-out (check Γ mot 'UNIVERSE)))
        (go `(the ,mot-out (ind-Absurd ,tgt-out ,mot-out))))]
     [`(= ,A ,from ,to)
      (go-on ((A-out (check Γ A 'UNIVERSE))
              (A-v (go (val-in-ctx Γ A-out)))
              (from-out (check Γ from A-v))
              (to-out (check Γ to A-v)))
        (go `(the U (= ,A-out ,from-out ,to-out))))]
     [`(replace ,tgt ,mot ,b)
      (go-on ((`(the ,tgt-t-out ,tgt-out) (synth Γ tgt)))
        (match (val-in-ctx Γ tgt-t-out)
          [(EQUAL Av fromv tov)
           (let ((x (fresh Γ 'x)))
             (go-on ((mot-out (check Γ
                                     mot
                                     (Π-type ((x Av)) 'UNIVERSE)))
                     (b-out (check Γ b (do-ap (val-in-ctx Γ mot-out)
                                               fromv))))
               (go `(the ,(read-back-type Γ (do-ap (val-in-ctx Γ mot-out)
                                                    tov))
                         (replace ,tgt-out ,mot-out ,b-out)))))]
          [non-equal
           (stop
            (src-loc e)
            `("Expected an expression with = type, but the type was"
              ,tgt-t-out))]))]
     [`(trans ,p1 ,p2)
      (go-on ((`(the ,p1-t-out ,p1-out) (synth Γ p1))
              (`(the ,p2-t-out ,p2-out) (synth Γ p2)))
        (match* ((val-in-ctx Γ p1-t-out) (val-in-ctx Γ p2-t-out))
          [((EQUAL Av from-v mid-v) (EQUAL Bv mid-v2 to-v))
           (go-on ((_ (same-type Γ (src-loc e) Av Bv))
                   (_ (convert Γ (src-loc e) Av mid-v mid-v2)))
             (go `(the ,(read-back-type Γ (EQUAL Av from-v to-v))
                       (trans ,p1-out ,p2-out))))]
          [(non=1 non=2)
           (stop (src-loc e)
                 `("Expected =, got"
                   ,(read-back-type Γ non=1) "and"
                   ,(read-back-type Γ non=2)))]))]
     [`(cong ,p ,f)
      (go-on ((`(the ,p-t-out ,p-out) (synth Γ p))
              (`(the ,f-t-out ,f-out) (synth Γ f)))
        (match (val-in-ctx Γ p-t-out)
          [(EQUAL Av from-v to-v)
           (match (val-in-ctx Γ f-t-out)
             [(PI x Bv c)
              (go-on ((_ (same-type Γ (src-loc e) Av Bv))
                      (Cv (go (val-of-closure c from-v)))
                      (f-v (go (val-in-ctx Γ f-out))))
                (go `(the (= ,(read-back-type Γ Cv)
                             ,(read-back Γ Cv (do-ap f-v from-v))
                             ,(read-back Γ Cv (do-ap f-v to-v)))
                          (cong ,p-out ,(read-back-type Γ Cv) ,f-out))))]
             [non-Pi
              (stop (src-loc e) `("Expected a function, got" ,(read-back-type Γ non-Pi)))])]
          [non= (stop (src-loc e) `("Expected =, got" ,(read-back-type Γ non=)))]))]
     [`(symm ,p)
      (go-on ((`(the ,p-t-out ,p-out) (synth Γ p)))
        (match (val-in-ctx Γ p-t-out)
          [(EQUAL Av from-v to-v)
           (go `(the ,(read-back-type Γ (EQUAL Av to-v from-v))
                     (symm ,p-out)))]
          [non=
           (stop (src-loc e)
                 `("Expected =, got" ,(read-back-type Γ non=)))]))]
     [`(ind-= ,tgt ,mot ,base)
      (go-on ((`(the ,tgt-t ,tgt-out) (synth Γ tgt)))
        (match (val-in-ctx Γ tgt-t)
          [(EQUAL Av from-v to-v)
           (go-on ((mot-out (check Γ mot (Π-type ((to Av)
                                                  (p (EQUAL Av from-v to)))
                                                 'UNIVERSE)))
                   (mot-v (go (val-in-ctx Γ mot-out)))
                   (base-out (check Γ base (do-ap (do-ap mot-v from-v)
                                                  (SAME from-v)))))
             (go `(the ,(read-back-type Γ (do-ap (do-ap mot-v to-v)
                                                 (val-in-ctx Γ tgt-out)))
                       (ind-= ,tgt-out
                              ,mot-out
                              ,base-out))))]
          [non= (stop (src-loc e) `("Expected evidence of equality, got "
                                    ,(read-back-type Γ non=)))]))]
     [`(Vec ,E ,len)
      (go-on ((E-out (check Γ E 'UNIVERSE))
              (len-out (check Γ len 'NAT)))
        (go `(the U (Vec ,E-out ,len-out))))]
     [`(head ,es)
      (go-on ((`(the ,es-type-out ,es-out)
               (synth Γ es)))
        (match (val-in-ctx Γ es-type-out)
          [(VEC Ev (ADD1 len-1))
           (go `(the ,(read-back-type Γ Ev)
                     (head ,es-out)))]
          [(VEC Ev non-add1)
           (stop
            (src-loc e)
            `("Expected a Vec with add1 at the top of the length, got"
              ,(read-back Γ 'NAT non-add1)))]
          [non-Vec
           (stop (src-loc e)
                 `("Expected a Vec, got"
                   ,(read-back-type Γ non-Vec)))]))]
     [`(tail ,es)
      (go-on ((`(the ,es-type-out ,es-out)
               (synth Γ es)))
        (match (val-in-ctx Γ es-type-out)
          [(VEC Ev (ADD1 len-1))
           (go `(the (Vec ,(read-back-type Γ Ev)
                          ,(read-back Γ 'NAT len-1))
                     (tail ,es-out)))]
          [(VEC Ev non-add1)
           (stop
            (src-loc e)
            `("Expected a Vec with add1 at the top of the length, got"
              ,(read-back Γ 'NAT non-add1)))]
          [non-Vec
           (stop (src-loc e)
                 `("Expected a Vec, got"
                   ,(read-back-type Γ non-Vec)))]))]
     [`(ind-Vec ,len ,vec ,mot ,b ,s)
      (go-on ((len-out (check Γ len 'NAT))
              (len-v (go (val-in-ctx Γ len-out)))
              (`(the ,vec-t ,vec-out) (synth Γ vec)))
        (match (val-in-ctx Γ vec-t)
          [(VEC Ev len2-v)
           (go-on ((_ (convert Γ (src-loc vec) 'NAT len-v len2-v))
                   (mot-out (check
                             Γ
                             mot
                             (Π-type ((k 'NAT)
                                      (es (VEC Ev k)))
                                     'UNIVERSE)))
                   (mot-val (go (val-in-ctx Γ mot-out)))
                   (b-out (check Γ
                                 b
                                 (do-ap (do-ap mot-val 'ZERO) 'VECNIL)))
                   (s-out (check
                           Γ
                           s
                           (ind-Vec-step-type Ev mot-val))))
             (go `(the ((,mot-out ,len-out) ,vec-out)
                       (ind-Vec ,len-out
                                ,vec-out
                                ,mot-out
                                ,b-out
                                ,s-out))))]
          [non-Vec
           (stop (src-loc e)
                 `("Expected a Vec, got"
                   ,(read-back-type Γ non-Vec)))]))]
     [`(Either ,L ,R)
      (go-on ((L-out (check Γ L 'UNIVERSE))
              (R-out (check Γ R 'UNIVERSE)))
        (go `(the U (Either ,L-out ,R-out))))]
     [`(ind-Either ,tgt ,mot ,l ,r)
      (go-on ((`(the ,tgt-t ,tgt-out) (synth Γ tgt)))
        (match (val-in-ctx Γ tgt-t)
          [(EITHER Lv Rv)
           (let ([x^ (fresh Γ 'x)])
             (go-on ((mot-out (check Γ mot (Π-type ((x (EITHER Lv Rv))) 'UNIVERSE)))
                     (mot-val (go (val-in-ctx Γ mot-out)))
                     (l-out (check Γ l (Π-type ((x Lv)) (do-ap mot-val (LEFT x)))))
                     (r-out (check Γ r (Π-type ((x Rv)) (do-ap mot-val (RIGHT x))))))
               (go `(the (,mot-out ,tgt-out)
                         (ind-Either ,tgt-out ,mot-out ,l-out ,r-out)))))]
          [non-Either
           (stop (src-loc e)
                 `("Expected an Either, but got a"
                   ,(read-back-type Γ non-Either)))]))]
     [`(the ,t ,e)
      (go-on ((t-out (is-type Γ t))
              (e-out (check Γ e (val-in-ctx Γ t-out))))
        (go `(the ,t-out ,e-out)))]
     ;;; Γ ⊢ f synth ~> (the (Pi ((x A)) B) f')
     ;;; Γ ⊢ a ∈ A ~> a'
     ;;; ----------------------------------------
     ;;; Γ ⊢ (f a) synth ~> (the B[a'/x] (f' a'))
     [`(,rator ,rand)
      #:when (src? rator)
      (go-on ((`(the ,rator-t ,rator-out)
               (synth Γ rator)))
        (match (val-in-ctx Γ rator-t)
          [(PI x A c)
           (go-on ((rand-out (check Γ rand A)))
             (go `(the ,(read-back-type
                         Γ
                         (val-of-closure c (val-in-ctx Γ rand-out)))
                       (,rator-out ,rand-out))))]
          [non-PI (stop (src-loc e)
                        `("Not a Π:" ,(read-back-type Γ non-PI)))]))]
     ;;; Γ ⊢ (f x y ...) synth ~> (the (Pi ((x A)) B) app')
     ;;; Γ ⊢ z ∈ A ~> z'
     ;;;---------------------------------------------------
     ;;; Γ ⊢ (f x y ... z) synth ~> (the B[z'/x] (app' z'))
     [(list rator rand0 rands ... rand)
      #:when (and (src? rator)
                  (andmap src? rands))
      (go-on ((`(the ,app0-t ,app0)
               (synth Γ (@ (not-for-info (src-loc e)) (list* rator rand0 rands)))))
        (match (val-in-ctx Γ app0-t)
          [(PI x A c)
           (go-on ((rand-out (check Γ rand A)))
             (go `(the ,(read-back-type
                         Γ
                         (val-of-closure c (val-in-ctx Γ rand-out)))
                       (,app0 ,rand-out))))]
          [non-PI (stop (src-loc e)
                        `("Not a Π:" ,(read-back-type Γ non-PI)))]))]
     [x
      (cond [(and (symbol? x) (var-name? x))
             (go-on ((x-tv (var-type Γ (src-loc e) x)))
               (begin (match (assv x Γ)
                        [(cons _ (def _ _))
                         (send-pie-info (src-loc e) 'definition)]
                        [_ (void)])
                      (go `(the ,(read-back-type Γ x-tv) ,x))))]
            [(number? x)
             (cond [(zero? x)
                    (go `(the Nat zero))]
                   [(positive? x)
                    (go-on ((n-1-out (check Γ
                                            (@ (src-loc e) (sub1 x))
                                            'NAT)))
                      (go `(the Nat (add1 ,n-1-out))))])]
            [else
             (stop (src-loc e)
                   `("Can't determine a type"))])]))
  (go-on ((`(the ,ty ,out) the-expr))
    (begin (send-pie-info (src-loc e) `(has-type ,ty))
           the-expr)))

(: check (-> Ctx Src Value (Perhaps Core)))
(define (check Γ e tv)
  (: out (Perhaps Core))
  (define out
   (match (src-stx e)
     [`(λ (,(binder x-loc x)) ,b)
      (match tv
        [(PI y A c)
         (go-on ((b-out (check (bind-free Γ x A)
                               b
                               (val-of-closure c (NEU A (N-var x))))))
           (begin ((pie-info-hook) x-loc `(binding-site ,(read-back-type Γ A)))
                  (go `(λ (,x) ,b-out))))]
        [non-PI
         (stop (src-loc e)
               `("Not a function type:"
                 ,(read-back-type Γ non-PI)))])]
     [`(λ (,x ,y . ,xs) ,b)
      (check Γ
             (@ (src-loc e)
                `(λ (,x)
                   ,(@ (not-for-info (src-loc e))
                       `(λ (,y . ,xs) ,b))))
             tv)]
     [`(cons ,a ,d)
      (match tv
        [(SIGMA x A c)
         (go-on ((a-out (check Γ a A))
                 (d-out (check Γ
                               d
                               (val-of-closure c (val-in-ctx Γ a-out)))))
           (go `(cons ,a-out ,d-out)))]
        [non-Sigma
         (stop (src-loc e)
               `("cons requires a Pair or Σ type, but was used as a"
                 ,(read-back-type Γ non-Sigma)))])]
     ['nil
      (match tv
        [(LIST E)
         (go 'nil)]
        [non-List
         (stop (src-loc e)
               `("nil requires a List type, but was used as a"
                 ,(read-back-type Γ non-List)))])]
     [`(same ,c)
      (match tv
        [(EQUAL Av fromv tov)
         (go-on ((c-out (check Γ c Av))
                 (v (go (val-in-ctx Γ c-out)))
                 (_ (convert Γ (src-loc c) Av fromv v))
                 (_ (convert Γ (src-loc c) Av tov v)))
           (go `(same ,c-out)))]
        [non-=
         (stop (src-loc e)
               `("same requires an = type, but was used as a"
                 ,(read-back-type Γ non-=)))])]
     ['vecnil
      (match tv
        [(VEC Ev 'ZERO)
         (go 'vecnil)]
        [(VEC Ev non-zero)
         (stop (src-loc e)
               `(vecnil
                 "requires that the length be zero, not"
                 ,(read-back Γ 'NAT non-zero)))]
        [non-Vec
         (stop (src-loc e)
               `(vecnil
                 "must be a Vec, but was used in a"
                 ,(read-back-type Γ non-Vec)
                 "context."))])]
     [`(vec:: ,h ,t)
      (match tv
        [(VEC Ev (ADD1 len-1))
         (go-on ((h-out (check Γ h Ev))
                 (t-out (check Γ t (VEC Ev len-1))))
           (go `(vec:: ,h-out ,t-out)))]
        [(VEC Ev non-add1)
         (stop (src-loc e)
               `("vec:: requires that the length have add1 on top, not"
                 ,(read-back Γ 'NAT non-add1)))]
        [non-Vec
         (stop (src-loc e)
               `("vec:: must be a Vec, but was used in a"
                 ,(read-back-type Γ non-Vec)
                 "context."))])]
     [`(left ,l)
      (match tv
        [(EITHER Lv Rv)
         (go-on ((l-out (check Γ l Lv)))
           (go `(left ,l-out)))]
        [non-Either
         (stop (src-loc e)
               `("left constructs an Either, but it was used where a"
                 ,(read-back-type Γ non-Either)
                 "was expected."))])]
     [`(right ,r)
      (match tv
        [(EITHER Lv Rv)
         (go-on ((r-out (check Γ r Rv)))
           (go `(right ,r-out)))]
        [non-Either
         (stop (src-loc e)
               `("right constructs an Either, but it was used where a"
                 ,(read-back-type Γ non-Either)
                 "was expected."))])]
     ['TODO
      (let ((ty (read-back-type Γ tv)))
        (begin (send-pie-info (src-loc e) `(TODO ,(read-back-ctx Γ) ,ty))
               (go (ann `(TODO ,(location->srcloc (src-loc e)) ,ty) Core))))]
     [else (go-on ((`(the ,t-out ,e-out) (synth Γ e))
                   (_ (same-type Γ (src-loc e) (val-in-ctx Γ t-out) tv)))
             (go e-out))]))
  (go-on ((ok out))
    (begin (send-pie-info (src-loc e) `(has-type ,(read-back-type Γ tv)))
           out)))

(: same-type (-> Ctx Loc Value Value (Perhaps Void)))
(define (same-type Γ where given expected)
  (let ([given-e (read-back-type Γ given)]
        [expected-e (read-back-type Γ expected)])
    (if (α-equiv? given-e expected-e)
        (go (void))
        (stop where
              `("Expected" ,(read-back-type Γ expected)
                           "but given" ,(read-back-type Γ given))))))

(: convert (-> Ctx Loc Value Value Value (Perhaps Void)))
(define (convert Γ where tv av bv)
  (let ([a (read-back Γ tv av)]
        [b (read-back Γ tv bv)])
    (if (α-equiv? a b)
        (go (void))
        (stop where
              `("The expressions"
                ,(read-back Γ tv av)
                "and"
                ,(read-back Γ tv bv)
                "are not the same"
                ,(read-back-type Γ tv))))))

;; --------------
;; Claims + defs

(: not-used (-> Ctx Loc Symbol (Perhaps #t)))
(define (not-used Γ where x)
  (if (pair? (assv x Γ))
      (stop where `("The name" ,x "is aready used."))
      (go #t)))

(: get-claim (-> Ctx Loc Symbol (Perhaps Value)))
(define (get-claim Γ where x)
  (match Γ
    ['() (stop where `("No claim:" ,x))]
    [(cons (cons y (claim tv)) Γ-next)
     #:when (eqv? x y)
     (go tv)]
    [(cons not-the-claim Γ-next)
     (get-claim Γ-next where x)]))

(: add-claim (-> Ctx Symbol Loc Src (Perhaps Ctx)))
(define (add-claim Γ f f-loc ty)
  (go-on ((_ (not-used Γ f-loc f))
          (ty-out (is-type Γ ty)))
    (go (cons (cons f (claim (val-in-ctx Γ ty-out)))
              Γ))))

(: remove-claim (-> Symbol Ctx Ctx))
(define (remove-claim x Γ)
  (match Γ
    ['() '()]
    [(cons (cons y (claim ty)) Γ-next)
     #:when (eqv? x y)
     (remove-claim x Γ-next)]
    [(cons (cons y b) Γ-next)
     #:when (not (eqv? x y))
     (cons (cons y b) (remove-claim x Γ-next))]))

(: add-def (-> Ctx Symbol Loc Src (Perhaps Ctx)))
(define (add-def Γ f f-loc expr)
  (go-on ((tv (get-claim Γ f-loc f))
          (expr-out (check Γ expr tv)))
    (go (bind-val (remove-claim f Γ) f tv (val-in-ctx Γ expr-out)))))


(: atom-ok? (-> Symbol Boolean))
(define (atom-ok? a)
  (all-ok-atom (string->list (symbol->string a))))

(: all-ok-atom (-> (Listof Char) Boolean))
(define (all-ok-atom cs)
  (cond
    [(null? cs) #t]
    [(or (char-alphabetic? (car cs))
         (eqv? (car cs) #\-))
     (all-ok-atom (cdr cs))]
    [else #f]))

(module+ test
  (require typed/rackunit)

  (check-true (atom-ok? 'food))
  (check-true (atom-ok? 'food---))
  (check-true (atom-ok? 'œ))
  (check-true (atom-ok? 'rugbrød))
  (check-true (atom-ok? 'देवनागरी))
  (check-true (atom-ok? '日本語))
  (check-true (atom-ok? 'atØm))
  (check-true (atom-ok? 'λ))
  (check-true (atom-ok? 'λάμβδα))


  (check-false (atom-ok? 'at0m))
  (check-false (atom-ok? '🛶)))

;; Local Variables:
;; eval: (put 'pmatch 'racket-indent-function 1)
;; eval: (put 'vmatch 'racket-indent-function 1)
;; eval: (put 'pmatch-who 'racket-indent-function 2)
;; eval: (put 'primitive 'racket-indent-function 1)
;; eval: (put 'derived 'racket-indent-function 0)
;; eval: (put 'data-constructor 'racket-indent-function 1)
;; eval: (put 'type-constructor 'racket-indent-function 1)
;; eval: (put 'tests-for 'racket-indent-function 1)
;; eval: (put 'hole 'racket-indent-function 1)
;; eval: (put 'Π 'racket-indent-function 1)
;; eval: (put 'Π* 'racket-indent-function 2)
;; eval: (put 'PI* 'racket-indent-function 1)
;; eval: (put 'Σ 'racket-indent-function 1)
;; eval: (put (intern "?") 'racket-indent-function 1)
;; eval: (put 'trace-type-checker 'racket-indent-function 1)
;; eval: (put 'go-on 'racket-indent-function 1)
;; eval: (setq whitespace-line-column 70)
;; End:
