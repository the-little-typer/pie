#lang typed/racket

;;; normalize.rkt
;;;
;;; This file implements normalization by evaluation.

(require "basics.rkt")
(require (for-syntax racket/base syntax/parse))
(require/typed "locations.rkt" (location->srcloc (-> Loc Srcloc)))
(provide (all-defined-out))

;; Call-by-need evaluation

(: later (-> Env Core Value))
(define (later ρ expr)
  (DELAY (box (DELAY-CLOS ρ expr))))

(: undelay (-> DELAY-CLOS Value))
(define (undelay c)
  (match c
    [(DELAY-CLOS ρ expr)
     (now (val-of ρ expr))]))

(: now (-> Value Value))
(define (now v)
  (match v
    [(DELAY (and b (box v)))
     (if (DELAY-CLOS? v)
         (let ((the-value (undelay v)))
           (set-box! b the-value)
           the-value)
         v)]
    [other other]))

(define-match-expander !!
  (lambda (pat-stx)
    (syntax-parse pat-stx
      [(!! p)
       (syntax/loc pat-stx
        (app now p))])))



(define-syntax (Π-type stx)
  (syntax-parse stx
    [(_ () ret) (syntax/loc stx ret)]
    [(_ ((x:id arg-t) b ...) ret)
     (syntax/loc stx
       (PI 'x arg-t (HO-CLOS (λ (x) (Π-type (b ...) ret)))))]))


(: do-ap (-> Value Value Value))
(define (do-ap rator-v rand-v)
  (match (now rator-v)
    [(LAM x c)
     (val-of-closure c rand-v)]
    [(NEU (!! (PI x A c))
          ne)
     (NEU (val-of-closure c rand-v)
          (N-ap ne (THE A rand-v)))]))

(: do-which-Nat (-> Value Value Value Value Value))
(define (do-which-Nat tgt-v b-tv b-v s-v)
  (match (now tgt-v)
    ['ZERO b-v]
    [(ADD1 n-1v)
     (do-ap s-v n-1v)]
    [(NEU (!! 'NAT) ne)
     (NEU b-tv
          (N-which-Nat ne
                       (THE b-tv b-v)
                       (THE (Π-type ((n 'NAT)) b-tv)
                            s-v)))]))

(: do-iter-Nat (-> Value Value Value Value Value))
(define (do-iter-Nat tgt-v b-tv b-v s-v)
  (match (now tgt-v)
    ['ZERO b-v]
    [(ADD1 n-1v)
     (do-ap s-v (do-iter-Nat n-1v b-tv b-v s-v))]
    [(NEU (!! 'NAT) ne)
     (NEU b-tv
          (N-iter-Nat ne
                      (THE b-tv b-v)
                      (THE (Π-type ((n b-tv)) b-tv)
                           s-v)))]))

(: do-rec-Nat (-> Value Value Value Value Value))
(define (do-rec-Nat tgt-v b-tv b-v s-v)
  (match (now tgt-v)
    ['ZERO b-v]
    [(ADD1 n-1v)
     (do-ap
            (do-ap s-v n-1v)
            (do-rec-Nat n-1v b-tv b-v s-v))]
    [(NEU (!! 'NAT) ne)
     (NEU b-tv
          (N-rec-Nat ne
                     (THE b-tv b-v)
                     (THE (Π-type ((n-1 'NAT)
                                   (ih b-tv))
                                  b-tv)
                          s-v)))]))


(: do-ind-Nat (-> Value Value Value Value Value))
(define (do-ind-Nat tgt-v mot-v b-v s-v)
  (match (now tgt-v)
    ['ZERO b-v]
    [(ADD1 n-1v)
     (do-ap (do-ap s-v n-1v)
            (do-ind-Nat n-1v mot-v b-v s-v))]
    [(NEU (!! 'NAT) ne)
     (NEU (do-ap mot-v tgt-v)
          (N-ind-Nat
           ne
           (THE (Π-type ((x 'NAT)) 'UNIVERSE)
                mot-v)
           (THE (do-ap mot-v 'ZERO) b-v)
           (THE (Π-type ((n-1 'NAT)
                         (ih (do-ap mot-v n-1)))
                        (do-ap mot-v (ADD1 n-1)))
                s-v)))]))

(: do-car (-> Value Value))
(define (do-car p-v)
  (match (now p-v)
    [(CONS a d) a]
    [(NEU (!! (SIGMA x A c)) ne)
     (NEU A (N-car ne))]))

(: do-cdr (-> Value Value))
(define (do-cdr p-v)
  (match (now p-v)
    [(CONS a d)
     d]
    [(NEU (!! (SIGMA x A c)) ne)
     (NEU (val-of-closure c (do-car p-v))
          (N-cdr ne))]))

(: do-ind-List (-> Value Value Value Value Value))
(define (do-ind-List tgt-v mot-v b-v s-v)
  (match (now tgt-v)
    ['NIL b-v]
    [(LIST:: h t)
     (do-ap
            (do-ap (do-ap s-v h) t)
            (do-ind-List t mot-v b-v s-v))]
    [(NEU (!! (LIST E)) ne)
     (let ([mot-tv (Π-type ((xs (LIST E))) 'UNIVERSE)])
       (NEU (do-ap mot-v tgt-v)
            (N-ind-List
             ne
             (THE mot-tv mot-v)
             (THE (do-ap mot-v 'NIL) b-v)
             (THE (Π-type ((h E)
                           (t (LIST E))
                           (ih (do-ap mot-v t)))
                          (do-ap mot-v (LIST:: h t)))
                  s-v))))]))

(: do-rec-List (-> Value Value Value Value Value))
(define (do-rec-List tgt-v b-tv b-v s-v)
  (match (now tgt-v)
    ['NIL b-v]
    [(LIST:: h t)
     (do-ap (do-ap (do-ap s-v h) t)
            (do-rec-List t b-tv b-v s-v))]
    [(NEU (!! (LIST E)) ne)
     (NEU b-tv
          (N-rec-List
           ne
           (THE b-tv b-v)
           (THE (Π-type ((h E)
                         (t (LIST E))
                         (ih b-tv))
                        b-tv)
                s-v)))]))

(: do-ind-Absurd (-> Value Value Value))
(define (do-ind-Absurd tgt-v mot-v)
  (match (now tgt-v)
    [(NEU (!! ABSURD) ne)
     (NEU mot-v
          (N-ind-Absurd ne (THE 'UNIVERSE mot-v)))]))

(: do-replace (-> Value Value Value Value))
(define (do-replace tgt-v mot-v b-v)
  (match (now tgt-v)
    [(SAME v)
     b-v]
    [(NEU (!! (EQUAL A-v from-v to-v))
          ne)
     (NEU (do-ap mot-v to-v)
          (N-replace ne
                     (THE (Π-type ((x A-v)) 'UNIVERSE)
                          mot-v)
                     (THE (do-ap mot-v from-v)
                          b-v)))]))

(: do-trans (-> Value Value Value))
(define (do-trans tgt-1v tgt-2v)
  (match* ((now tgt-1v) (now tgt-2v))
    [((SAME v) (SAME _))
     (SAME v)]
    [((SAME from-v) (NEU (!! (EQUAL A-v _ to-v)) ne2))
     (NEU (EQUAL A-v from-v to-v)
           (N-trans2 (THE (EQUAL A-v from-v from-v) (SAME from-v))
                      ne2))]
    [((NEU (!! (EQUAL A-v from-v _)) ne1) (SAME to-v))
     (NEU (EQUAL A-v from-v to-v)
          (N-trans1 ne1 (THE (EQUAL A-v to-v to-v) (SAME to-v))))]
    [((NEU (!! (EQUAL A-v from-v _)) ne1) (NEU (!! (EQUAL _ _ to-v)) ne2))
     (NEU (EQUAL A-v from-v to-v)
          (N-trans12 ne1 ne2))]))

(: do-cong (-> Value Value Value Value))
(define (do-cong tgt-v B-v fun-v)
  (match (now tgt-v)
    [(SAME v)
     (SAME (do-ap fun-v v))]
    [(NEU (!! (EQUAL A-v from-v to-v)) ne)
     (NEU (EQUAL B-v (do-ap fun-v from-v) (do-ap fun-v to-v))
          (N-cong ne (THE (Π-type ((x A-v)) B-v) fun-v)))]))

(: do-symm (-> Value Value))
(define (do-symm tgt-v)
  (match (now tgt-v)
    [(SAME v) (SAME v)]
    [(NEU (!! (EQUAL A-v from-v to-v))
           ne)
     (NEU (EQUAL A-v to-v from-v)
           (N-symm ne))]))

(: do-ind-= (->  Value Value Value Value))
(define (do-ind-= tgt-v motive-v base-v)
  (match (now tgt-v)
    [(SAME v) base-v]
    [(NEU (!! (EQUAL A from to)) ne)
     (NEU (do-ap (do-ap motive-v to) tgt-v)
          (N-ind-= ne
                   (THE (Π-type ((to A)
                                 (p (EQUAL A from to)))
                                'UNIVERSE)
                        motive-v)
                   (THE (do-ap (do-ap motive-v from)
                               (SAME from))
                        base-v)))]))

(: do-head (-> Value Value))
(define (do-head tgt-v)
  (match (now tgt-v)
    [(VEC:: hv tv) hv]
    [(NEU (!! (VEC Ev (!! (ADD1 len-1v))))
           ne)
     (NEU Ev (N-head ne))]))

(: do-tail (-> Value Value))
(define (do-tail tgt-v)
  (match (now tgt-v)
    [(VEC:: hv tv) tv]
    [(NEU (!! (VEC Ev (!! (ADD1 len-1v)))) ne)
     (NEU (VEC Ev len-1v) (N-tail ne))]))

(: ind-Vec-step-type (-> Value Value Value))
(define (ind-Vec-step-type Ev mot-v)
  (Π-type ((k 'NAT)
           (e Ev)
           (es (VEC Ev k))
           (ih (do-ap (do-ap mot-v k) es)))
          (do-ap (do-ap mot-v (ADD1 k)) (VEC:: e es))))

(: do-ind-Vec (-> Value Value Value Value Value Value))
(define (do-ind-Vec len-v vec-v mot-v b-v s-v)
  (match* ((now len-v) (now vec-v))
    [('ZERO 'VECNIL) b-v]
    [((ADD1 len-1-v) (VEC:: h t))
     (do-ap (do-ap (do-ap (do-ap s-v len-1-v) h) (do-tail vec-v))
            (do-ind-Vec len-1-v t mot-v b-v s-v))]
    [((NEU (!! 'NAT) len) (NEU (!! (VEC Ev _)) ne))
     (NEU (do-ap (do-ap mot-v len-v) vec-v)
          (N-ind-Vec12 len
                       ne
                       (THE (Π-type ((k 'NAT)
                                     (es (VEC Ev k)))
                              'UNIVERSE)
                            mot-v)
                       (THE (do-ap (do-ap mot-v 'ZERO) 'VECNIL) b-v)
                       (THE (ind-Vec-step-type Ev mot-v)
                        s-v)))]
    [(len-v (NEU (!! (VEC Ev _)) ne))
     (NEU (do-ap (do-ap mot-v len-v) vec-v)
          (N-ind-Vec2 (THE 'NAT len-v)
                      ne
                      (THE (Π-type ((k 'NAT)
                                    (es (VEC Ev k)))
                                   'UNIVERSE)
                           mot-v)
                      (THE (do-ap (do-ap mot-v 'ZERO) 'VECNIL)
                           b-v)
                      (THE (ind-Vec-step-type Ev mot-v) s-v)))]))

(: do-ind-Either (-> Value Value Value Value Value))
(define (do-ind-Either tgt mot l r)
  (match (now tgt)
    [(LEFT x)
     (do-ap l x)]
    [(RIGHT x)
     (do-ap r x)]
    [(NEU (!! (EITHER Lv Rv)) ne)
     (let ([mot-tv (Π-type ((x (EITHER Lv Rv))) 'UNIVERSE)])
       (NEU (do-ap mot tgt)
            (N-ind-Either ne
                          (THE mot-tv mot)
                          (THE (Π-type ((x Lv))
                                       (do-ap mot (LEFT x)))
                               l)
                          (THE (Π-type ((x Rv))
                                       (do-ap mot (RIGHT x)))
                               r))))]))

(: val-of (-> Env Core Value))
(define (val-of ρ e)
  (match e
    ['U 'UNIVERSE]
    ['Nat 'NAT]
    ['zero 'ZERO]
    [`(add1 ,n) (ADD1 (later ρ n))]
    [`(Π ((,x ,A)) ,B)
     (let ([A-v (later ρ A)])
       (PI x A-v (FO-CLOS ρ x B)))]
    [`(λ (,x) ,b)
     (LAM x (FO-CLOS ρ x b))]
    [`(which-Nat ,tgt (the ,b-t ,b) ,s)
     (do-which-Nat (later ρ tgt)
                   (later ρ b-t)
                   (later ρ b)
                   (later ρ s))]
    [`(iter-Nat ,tgt (the ,b-t ,b) ,s)
     (do-iter-Nat (later ρ tgt)
                  (later ρ b-t)
                  (later ρ b)
                  (later ρ s))]
    [`(rec-Nat ,tgt (the ,b-t ,b) ,s)
     (do-rec-Nat (later ρ tgt)
                 (later ρ b-t)
                 (later ρ b)
                 (later ρ s))]
    [`(ind-Nat ,tgt ,mot ,b ,s)
     (do-ind-Nat (later ρ tgt)
                 (later ρ mot)
                 (later ρ b)
                 (later ρ s))]
    ['Atom 'ATOM]
    [`(Σ ((,x ,A)) ,D)
     (let ([A-v (later ρ A)])
      (SIGMA x A-v (FO-CLOS ρ x D)))]
    [`(cons ,a ,d) (CONS (later ρ a) (later ρ d))]
    [`(car ,p) (do-car (later ρ p))]
    [`(cdr ,p) (do-cdr (later ρ p))]
    [`(quote ,a) #:when (symbol? a) (QUOTE a)]
    ['Trivial 'TRIVIAL]
    ['sole 'SOLE]
    ['nil 'NIL]
    [`(:: ,h ,t) (LIST:: (later ρ h) (later ρ t))]
    [`(List ,E) (LIST (later ρ E))]
    [`(ind-List ,tgt ,mot ,b ,s)
     (do-ind-List (later ρ tgt)
                  (later ρ mot)
                  (later ρ b)
                  (later ρ s))]
    [`(rec-List ,tgt (the ,b-t ,b) ,s)
     (do-rec-List (later ρ tgt)
                  (later ρ b-t)
                  (later ρ b)
                  (later ρ s))]
    [`Absurd 'ABSURD]
    [`(ind-Absurd ,tgt ,mot)
     (do-ind-Absurd (later ρ tgt) (later ρ mot))]
    [`(= ,A ,from ,to)
     (EQUAL (later ρ A) (later ρ from) (later ρ to))]
    [`(same ,e)
     (SAME (later ρ e))]
    [`(replace ,tgt ,mot ,b)
     (do-replace (later ρ tgt) (later ρ mot) (later ρ b))]
    [`(trans ,p1 ,p2)
     (do-trans (later ρ p1) (later ρ p2))]
    [`(cong ,p1 ,p2 ,p3)
     (do-cong (later ρ p1) (later ρ p2) (later ρ p3))]
    [`(symm ,p)
     (do-symm (later ρ p))]
    [`(ind-= ,tgt ,mot ,b)
     (do-ind-= (later ρ tgt) (later ρ mot) (later ρ b))]
    [`(Vec ,E ,len)
     (VEC (later ρ E) (later ρ len))]
    ['vecnil 'VECNIL]
    [`(vec:: ,h ,t) (VEC:: (later ρ h) (later ρ t))]
    [`(head ,es) (do-head (later ρ es))]
    [`(tail ,es) (do-tail (later ρ es))]
    [`(ind-Vec ,len ,es ,mot ,b ,s)
     (do-ind-Vec (later ρ len)
                 (later ρ es)
                 (later ρ mot)
                 (later ρ b)
                 (later ρ s))]
    [`(Either ,L ,R) (EITHER (later ρ L) (later ρ R))]
    [`(left ,l) (LEFT (later ρ l))]
    [`(right ,r) (RIGHT (later ρ r))]
    [`(ind-Either ,tgt ,mot ,l ,r)
     (do-ind-Either (later ρ tgt)
                    (later ρ mot)
                    (later ρ l)
                    (later ρ r))]
    [`(,rator ,rand)
     (do-ap (later ρ rator) (later ρ rand))]
    [`(TODO ,where ,type)
     (NEU (later ρ type) (N-TODO where (later ρ type)))]
    [x
     (if (and (symbol? x) (var-name? x))
         (var-val ρ x)
         (error (format "No evaluator for ~a" x)))]))

(: read-back-ctx (-> Ctx Serializable-Ctx))
(define (read-back-ctx Γ)
  (match Γ
    ['()
     '()]
    [(cons (cons x (free t)) Γ-next)
     (cons (list x (list 'free (read-back-type Γ-next t)))
           (read-back-ctx Γ-next))]
    [(cons (cons x (def t v)) Γ-next)
     (cons (list x (list 'def (read-back-type Γ-next t) (read-back Γ-next t v)))
           (read-back-ctx Γ-next))]
    [(cons (cons x (claim t)) Γ-next)
     (cons (list x (list 'claim (read-back-type Γ-next t)))
           (read-back-ctx Γ-next))]))

(: val-of-ctx (-> Serializable-Ctx Ctx))
(define (val-of-ctx ctx-list)
  (match ctx-list
    ['() '()]
    [(cons (list x b) ctx-tail)
     (let ([Γ (val-of-ctx ctx-tail)])
       (cons (cons x
                   (match b
                     [(list 'free t) (free (val-in-ctx Γ t))]
                     [(list 'def t e) (def (val-in-ctx Γ t) (val-in-ctx Γ e))]
                     [(list 'claim t) (claim (val-in-ctx Γ t))]))
             Γ))]))

(: val-in-ctx (-> Ctx Core Value))
(define (val-in-ctx Γ e)
  (val-of (ctx->env Γ) e))

(: read-back-type (-> Ctx Value Core))
(define (read-back-type Γ tv)
  (match (now tv)
    ['UNIVERSE 'U]
    ['NAT 'Nat]
    [(PI x A c)
     (let ((A-e (read-back-type Γ A))
           (x^ (fresh Γ x)))
       `(Π ((,x^ ,A-e))
          ,(let ((Γ/x^ (bind-free Γ x^ A)))
             (read-back-type Γ/x^ (val-of-closure c (NEU A (N-var x^)))))))]
    ['ATOM 'Atom]
    [(SIGMA x A c)
     (let ((A-e (read-back-type Γ A))
           (x^ (fresh Γ x)))
       `(Σ ((,x^ ,A-e))
          ,(let ((Γ/x^ (bind-free Γ x^ A)))
             (read-back-type Γ/x^ (val-of-closure c (NEU A (N-var x^)))))))]
    ['TRIVIAL 'Trivial]
    [(LIST E) `(List ,(read-back-type Γ E))]
    ['ABSURD 'Absurd]
    [(EQUAL Av fromv tov)
     `(= ,(read-back-type Γ Av)
         ,(read-back Γ Av fromv)
         ,(read-back Γ Av tov))]
    [(VEC Ev lenv)
     `(Vec ,(read-back-type Γ Ev) ,(read-back Γ 'NAT lenv))]
    [(EITHER Lv Rv)
     `(Either ,(read-back-type Γ Lv) ,(read-back-type Γ Rv))]
    [(NEU UNIVERSE ne)
     (read-back-neutral Γ ne)]))

(: read-back (-> Ctx Value Value Core))
(define (read-back Γ tv v)
  (match* ((now tv) (now v))
    [('UNIVERSE v) (read-back-type Γ v)]
    [('NAT 'ZERO) 'zero]
    [('NAT (ADD1 n-1))
     `(add1 ,(read-back Γ 'NAT n-1))]
    [((PI x A c) f)
     (let ((y (match f
                [(LAM y _) y]
                [_ x])))
       (let ((x^ (fresh Γ y)))
         `(λ (,x^)
            ,(read-back
              (bind-free Γ x^ A)
              (val-of-closure c (NEU A (N-var x^)))
              (do-ap f (NEU A (N-var x^)))))))]
    [((SIGMA x A c) p-v)
     (let ((the-car (do-car p-v)))
      `(cons ,(read-back Γ A the-car)
             ,(read-back Γ
                         (val-of-closure c the-car)
                         (do-cdr p-v))))]
    [('ATOM (QUOTE a))
     `(quote ,a)]
    [('TRIVIAL _) 'sole] ;; η-expansion
    [((LIST E) 'NIL) 'nil]
    [((LIST E) (LIST:: h t))
     `(:: ,(read-back Γ E h) ,(read-back Γ (LIST E) t))]
    [('ABSURD (NEU _ ne))
     ;; This type annotation is half of the η law. See the
     ;; implementation of α-equiv? for the other half.
     `(the Absurd ,(read-back-neutral Γ ne))]
    [((EQUAL Av _ _) (SAME v))
     `(same ,(read-back Γ Av v))]
    [((VEC Ev (!! 'ZERO)) _) 'vecnil]
    [((VEC Ev (!! (ADD1 len-1v))) (VEC:: h t))
     `(vec:: ,(read-back Γ Ev h)
             ,(read-back Γ (VEC Ev len-1v) t))]
    [((EITHER Lv Rv) (LEFT lv))
     `(left ,(read-back Γ Lv lv))]
    [((EITHER Lv Rv) (RIGHT rv))
     `(right ,(read-back Γ Rv rv))]
    [(_ (NEU _ ne))
     (read-back-neutral Γ ne)]))

(: read-back-neutral (-> Ctx Neutral Core))
(define (read-back-neutral Γ ne)
  (match ne
    [(N-which-Nat tgt (THE b-tv b-v) (THE s-tv s-v))
     `(which-Nat ,(read-back-neutral Γ tgt)
                 (the ,(read-back-type Γ b-tv)
                      ,(read-back Γ b-tv b-v))
                 ,(read-back Γ s-tv s-v))]
    [(N-iter-Nat tgt (THE b-tv b-v) (THE s-tv s-v))
     `(iter-Nat ,(read-back-neutral Γ tgt)
                (the ,(read-back-type Γ b-tv)
                     ,(read-back Γ b-tv b-v))
                ,(read-back Γ s-tv s-v))]
    [(N-rec-Nat tgt (THE b-tv b-v) (THE s-tv s-v))
     `(rec-Nat ,(read-back-neutral Γ tgt)
               (the ,(read-back-type Γ b-tv)
                    ,(read-back Γ b-tv b-v))
               ,(read-back Γ s-tv s-v))]
    [(N-ind-Nat tgt
                (THE mot-tv mot-v)
                (THE b-tv b-v)
                (THE s-tv s-v))
     `(ind-Nat ,(read-back-neutral Γ tgt)
               ,(read-back Γ mot-tv mot-v)
               ,(read-back Γ b-tv b-v)
               ,(read-back Γ s-tv s-v))]
    [(N-car tgt)
     (ann `(car ,(read-back-neutral Γ tgt)) Core)]
    [(N-cdr tgt)
     (ann `(cdr ,(read-back-neutral Γ tgt)) Core)]
    [(N-ind-List tgt (THE mot-t mot) (THE b-t b) (THE s-t s))
     `(ind-List ,(read-back-neutral Γ tgt)
                ,(read-back Γ mot-t mot)
                ,(read-back Γ b-t b)
                ,(read-back Γ s-t s))]
    [(N-rec-List tgt (THE b-t b) (THE s-t s))
     `(rec-List ,(read-back-neutral Γ tgt)
                (the ,(read-back-type Γ b-t)
                     ,(read-back Γ b-t b))
                ,(read-back Γ s-t s))]
    [(N-ind-Absurd tgt (THE tv ttv))
     ;; Here's some Absurd η. The rest is in α-equiv?.
     `(ind-Absurd (the Absurd ,(read-back-neutral Γ tgt))
                  ,(read-back Γ tv ttv))]
    [(N-replace tgt (THE mot-tv mot-v) (THE b-tv b-v))
     `(replace ,(read-back-neutral Γ tgt)
               ,(read-back Γ mot-tv mot-v)
               ,(read-back Γ b-tv b-v))]
    [(N-trans12 p1 p2)
     `(trans ,(read-back-neutral Γ p1) ,(read-back-neutral Γ p2))]
    [(N-trans1 ne (THE t v))
     `(trans ,(read-back-neutral Γ ne) ,(read-back Γ t v))]
    [(N-trans2 (THE t v) ne)
     `(trans ,(read-back Γ t v) ,(read-back-neutral Γ ne))]
    [(N-cong ne (THE (PI y Av c) v))
     `(cong ,(read-back-neutral Γ ne)
            ,(read-back-type Γ (val-of-closure c 'ABSURD))
            ,(read-back Γ (PI y Av c) v))]
    [(N-symm ne)
     `(symm ,(read-back-neutral Γ ne))]
    [(N-ind-= ne (THE mot-t mot) (THE b-t b))
     `(ind-= ,(read-back-neutral Γ ne)
             ,(read-back Γ mot-t mot)
             ,(read-back Γ b-t b))]
    [(N-head ne)
     `(head ,(read-back-neutral Γ ne))]
    [(N-tail ne)
     `(tail ,(read-back-neutral Γ ne))]
    [(N-ind-Vec1 len (THE es-t es-v) (THE mot-t mot) (THE b-t b) (THE s-t s))
     `(ind-Vec ,(read-back-neutral Γ len)
               ,(read-back Γ es-t es-v)
               ,(read-back Γ mot-t mot)
               ,(read-back Γ b-t b)
               ,(read-back Γ s-t s))]
    [(N-ind-Vec2 (THE len-t len-v) es (THE mot-t mot) (THE b-t b) (THE s-t s))
     `(ind-Vec ,(read-back Γ len-t len-v)
               ,(read-back-neutral Γ es)
               ,(read-back Γ mot-t mot)
               ,(read-back Γ b-t b)
               ,(read-back Γ s-t s))]
    [(N-ind-Vec12 len es (THE mot-t mot) (THE b-t b) (THE s-t s))
     `(ind-Vec ,(read-back-neutral Γ len)
               ,(read-back-neutral Γ es)
               ,(read-back Γ mot-t mot)
               ,(read-back Γ b-t b)
               ,(read-back Γ s-t s))]
    [(N-ind-Either tgt (THE mot-tv mot-v) (THE l-tv l-v) (THE r-tv r-v))
     `(ind-Either ,(read-back-neutral Γ tgt)
                  ,(read-back Γ mot-tv mot-v)
                  ,(read-back Γ l-tv l-v)
                  ,(read-back Γ r-tv r-v))]
    [(N-ap tgt (THE arg-tv arg-v))
     `(,(read-back-neutral Γ tgt)
       ,(read-back Γ arg-tv arg-v))]
    [(N-var x) x]
    [(N-TODO where tyv) `(TODO ,where ,(read-back-type Γ tyv))]))

(: val-of-closure (-> Closure Value Value))
(define (val-of-closure c v)
  (match c
    [(FO-CLOS ρ x e)
     (val-of (extend-env ρ x v) e)]
    [(HO-CLOS fun) (fun v)]))



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
