#lang racket
;;; This module contains the parsers that convert Pie concrete syntax
;;; into source-code-annotated Pie input ASTs.


(require "basics.rkt" "typechecker.rkt"
         (prefix-in kw: "pie-info.rkt")
         racket/match
         syntax/parse
         (for-syntax syntax/parse)
         (for-syntax racket/syntax))
(provide (all-defined-out))

(define-syntax-class pie-id
  #:description "valid Pie name"
  (pattern name:id #:when (var-name? (syntax->datum #'name))))

(begin-for-syntax
  (define-syntax-class pie-id
    #:description "valid Pie name"
    (pattern name:id #:when (var-name? (syntax->datum #'name)))))

(define (syntax->srcloc stx)
  (syntax->location stx)
  #;
  (srcloc (syntax-source stx)
          (syntax-line stx)
          (syntax-column stx)
          (syntax-position stx)
          (syntax-span stx)))

(define (binding-site id)
  (binder (syntax->srcloc id) (syntax->datum id)))

(define (make-U loc)
  (@ (syntax->srcloc loc) 'U))


(define (make--> loc A B Cs)
  (@ (syntax->srcloc loc)
     (list* '-> A B Cs)))


(define (make-Nat loc)
  (@ (syntax->srcloc loc) 'Nat))


(define (make-zero loc)
  (@ (syntax->srcloc loc) 'zero))


(define (make-add1 loc n)
  (@ (syntax->srcloc loc) `(add1 ,n)))


(define (make-lambda loc xs body)
  (@ (syntax->srcloc loc) `(λ ,xs ,body)))


(define (make-Pi loc args body)
  (@ (syntax->srcloc loc) `(Π ,args ,body)))


(define (make-Sigma loc args body)
  (@ (syntax->srcloc loc) `(Σ ,args ,body)))


(define (typed-binders A Bs)
  (cons A Bs))


(define (make-ap loc rator rand0 rands)
  (@ (syntax->srcloc loc)
     (list* rator rand0 rands)))


(define (make-Atom loc)
  (@ (syntax->srcloc loc) 'Atom))


(define (make-Trivial loc)
  (@ (syntax->srcloc loc) 'Trivial))


(define (make-sole loc)
  (@ (syntax->srcloc loc) 'sole))


(define (make-List loc E)
  (@ (syntax->srcloc loc) `(List ,E)))


(define (make-Vec loc E len)
  (@ (syntax->srcloc loc) `(Vec ,E ,len)))


(define (make-Either loc L R)
  (@ (syntax->srcloc loc) `(Either ,L ,R)))


(define (make-nil loc)
  (@ (syntax->srcloc loc) 'nil))


(define (make-:: loc x xs)
  (@ (syntax->srcloc loc) `(:: ,x ,xs)))


(define (make-vec:: loc x xs)
  (@ (syntax->srcloc loc) `(vec:: ,x ,xs)))


(define (make-vecnil loc)
  (@ (syntax->srcloc loc) 'vecnil))


(define (make-Absurd loc)
  (@ (syntax->srcloc loc) 'Absurd))


(define (make-Pair loc A B)
  (@ (syntax->srcloc loc) `(Pair ,A ,B)))


(define (make-cons loc a d)
  (@ (syntax->srcloc loc) `(cons ,a ,d)))


(define (make-the loc a d)
  (@ (syntax->srcloc loc) `(the ,a ,d)))


(define (make-ind-Absurd loc a d)
  (@ (syntax->srcloc loc) `(ind-Absurd ,a ,d)))


(define (make-trans loc p1 p2)
  (@ (syntax->srcloc loc) `(trans ,p1 ,p2)))


(define (make-cong loc p1 p2)
  (@ (syntax->srcloc loc) `(cong ,p1 ,p2)))

(define (make-ind-= loc tgt mot base)
  (@ (syntax->srcloc loc) `(ind-= ,tgt ,mot ,base)))

(define (make-which-Nat loc e1 e2 e3)
  (@ (syntax->srcloc loc) `(which-Nat ,e1 ,e2 ,e3)))


(define (make-iter-Nat loc e1 e2 e3)
  (@ (syntax->srcloc loc) `(iter-Nat ,e1 ,e2 ,e3)))


(define (make-rec-Nat loc e1 e2 e3)
  (@ (syntax->srcloc loc) `(rec-Nat ,e1 ,e2 ,e3)))


(define (make-ind-Nat loc e1 e2 e3 e4)
  (@ (syntax->srcloc loc) `(ind-Nat ,e1 ,e2 ,e3 ,e4)))


(define (make-rec-List loc e1 e2 e3)
  (@ (syntax->srcloc loc) `(rec-List ,e1 ,e2 ,e3)))


(define (make-ind-List loc e1 e2 e3 e4)
  (@ (syntax->srcloc loc) `(ind-List ,e1 ,e2 ,e3 ,e4)))


(define (make-ind-Either loc e1 e2 e3 e4)
  (@ (syntax->srcloc loc) `(ind-Either ,e1 ,e2 ,e3 ,e4)))


(define (make-ind-Vec loc e1 e2 e3 e4 e5)
  (@ (syntax->srcloc loc) `(ind-Vec ,e1 ,e2 ,e3 ,e4 ,e5)))


(define (make-= loc e1 e2 e3)
  (@ (syntax->srcloc loc) `(= ,e1 ,e2 ,e3)))


(define (make-replace loc e1 e2 e3)
  (@ (syntax->srcloc loc) `(replace ,e1 ,e2 ,e3)))


(define (make-symm loc e)
  (@ (syntax->srcloc loc) `(symm ,e)))


(define (make-head loc e)
  (@ (syntax->srcloc loc) `(head ,e)))


(define (make-tail loc e)
  (@ (syntax->srcloc loc) `(tail ,e)))


(define (make-same loc e)
  (@ (syntax->srcloc loc) `(same ,e)))


(define (make-left loc e)
  (@ (syntax->srcloc loc) `(left ,e)))


(define (make-right loc e)
  (@ (syntax->srcloc loc) `(right ,e)))


(define (make-car loc e)
  (@ (syntax->srcloc loc) `(car ,e)))


(define (make-cdr loc e)
  (@ (syntax->srcloc loc) `(cdr ,e)))


(define (make-quote loc a)
  (@ (syntax->srcloc loc) `(quote ,a)))


(define (make-var-ref loc a)
  (@ (syntax->srcloc loc) a))


(define (make-nat-literal loc n)
  (@ (syntax->srcloc loc) n))


(define (make-TODO loc)
  (@ (syntax->srcloc loc) 'TODO))


(define (parse-pie stx)
  (syntax-parse stx
    #:datum-literals (U
                      Nat zero add1
                      which-Nat iter-Nat rec-Nat ind-Nat
                      → -> Pi Π ∏ the lambda λ Atom quote
                      cons car cdr Sigma Σ Pair
                      Trivial sole
                      List :: nil ind-List rec-List
                      Absurd ind-Absurd
                      = same replace symm trans cong ind-=
                      head tail Vec vec:: vecnil ind-Vec
                      Either left right ind-Either
                      TODO)
    [U
     (make-U stx)]
    [Nat
     (make-Nat stx)]
    [(→ ~! A B C ...)
     (make--> stx
              (parse-pie #'A)
              (parse-pie #'B)
              (map parse-pie (syntax->list #'(C ...))))]
    [(-> ~! A B C ...)
     (make--> stx
              (parse-pie #'A)
              (parse-pie #'B)
              (map parse-pie (syntax->list #'(C ...))))]
    [zero
     (make-zero stx)]
    [(add1 ~! n)
     (make-add1 stx (parse-pie #'n))]
    [(lambda ~! ((~describe "argument name" x0:pie-id)
                 (~describe "argument name" x:pie-id)
                 ...)
        b)
     (make-lambda stx
                  (map binding-site (syntax->list #'(x0 x ...)))
                  (parse-pie #'b))]
    [(λ ~! ((~describe "argument name" x0:pie-id)
            (~describe "argument name" x:pie-id)
            ...)
        b)
     (make-lambda stx
                  (map binding-site (syntax->list #'(x0 x ...)))
                  (parse-pie #'b))]
    [(Pi ~! more ...)
     (parse-pie #'(Π more ...))]
    [(∏ ~! more ...)
     (parse-pie #'(Π more ...))]
    [(Π ~! (~describe "argument names and types"
                      ((x0:pie-id A0) (x:pie-id A) ...))
        (~describe "result type" B))
     (make-Pi stx
              (typed-binders (list (binding-site #'x0) (parse-pie #'A0))
                             (for/list ([b (syntax->list #'((x A) ...))])
                               (match (syntax->list b)
                                 [(list x A)
                                  (list (binding-site x)
                                        (parse-pie A))])))
              (parse-pie #'B))]
    [(Sigma ~! more ...)
     (parse-pie (syntax/loc stx (Σ more ...)))]
    [(Σ ~! (~describe "car names and types"
                      ((x0:pie-id A0) (x:pie-id A) ...))
        (~describe "cdr type" B))
     (make-Sigma stx
                 (typed-binders (list (binding-site #'x0) (parse-pie #'A0))
                                (for/list ([b (syntax->list #'((x A) ...))])
                                  (match (syntax->list b)
                                    [(list x A)
                                     (list (binding-site x)
                                           (parse-pie A))])))
                 (parse-pie #'B))]
    [(Pair ~! A D)
     (make-Pair stx (parse-pie #'A) (parse-pie #'D))]
    [(cons ~! a d)
     (make-cons stx (parse-pie #'a) (parse-pie #'d))]
    [(car ~! p)
     (make-car stx (parse-pie #'p))]
    [(cdr ~! p)
     (make-cdr stx (parse-pie #'p))]
    [(the ~! t e)
     (make-the stx (parse-pie #'t) (parse-pie #'e))]
    [(which-Nat ~! tgt b s)
     (make-which-Nat stx (parse-pie #'tgt) (parse-pie #'b) (parse-pie #'s))]
    [(rec-Nat ~! tgt b s)
     (make-rec-Nat stx (parse-pie #'tgt) (parse-pie #'b) (parse-pie #'s))]
    [(iter-Nat ~! tgt b s)
     (make-iter-Nat stx (parse-pie #'tgt) (parse-pie #'b) (parse-pie #'s))]
    [(ind-Nat ~! tgt mot b s)
     (make-ind-Nat stx (parse-pie #'tgt) (parse-pie #'mot) (parse-pie #'b) (parse-pie #'s))]
    [Atom
     (make-Atom stx)]
    [(quote ~! a:id)
     (make-quote stx (syntax->datum #'a))]
    [Trivial
     (make-Trivial stx)]
    [sole
     (make-sole stx)]
    [(List ~! E)
     (make-List stx (parse-pie #'E))]
    [nil
     (make-nil stx)]
    [(:: ~! e es)
     (make-:: stx (parse-pie #'e) (parse-pie #'es))]
    [(ind-List ~! tgt mot b s)
     (make-ind-List stx (parse-pie #'tgt) (parse-pie #'mot) (parse-pie #'b) (parse-pie #'s))]
    [(rec-List ~! tgt b s)
     (make-rec-List stx (parse-pie #'tgt) (parse-pie #'b) (parse-pie #'s))]
    [x:pie-id
     (make-var-ref stx (syntax->datum #'x.name))]
    [Absurd
     (make-Absurd stx)]
    [(ind-Absurd ~! tgt mot)
     (make-ind-Absurd stx (parse-pie #'tgt) (parse-pie #'mot))]
    [n:nat
     (make-nat-literal stx (syntax->datum #'n))]
    [(= ~! A from to)
     (make-= stx (parse-pie #'A) (parse-pie #'from) (parse-pie #'to))]
    [(same ~! e)
     (make-same stx (parse-pie #'e))]
    [(replace ~! tgt mot b)
     (make-replace stx (parse-pie #'tgt) (parse-pie #'mot) (parse-pie #'b))]
    [(trans ~! p1 p2)
     (make-trans stx (parse-pie #'p1) (parse-pie #'p2))]
    [(cong ~! p1 p2)
     (make-cong stx (parse-pie #'p1) (parse-pie #'p2))]
    [(ind-= ~! (~describe "target" tgt) (~describe "motive" mot) (~describe "base" base))
     (make-ind-= stx (parse-pie #'tgt) (parse-pie #'mot) (parse-pie #'base))]
    [(symm ~! p)
     (make-symm stx (parse-pie #'p))]
    [(Vec ~! E len)
     (make-Vec stx (parse-pie #'E) (parse-pie #'len))]
    [vecnil
     (make-vecnil stx)]
    [(vec:: ~! h t)
     (make-vec:: stx (parse-pie #'h) (parse-pie #'t))]
    [(head ~! es)
     (make-head stx (parse-pie #'es))]
    [(tail ~! es)
     (make-tail stx (parse-pie #'es))]
    [(ind-Vec ~! k xs m b s)
     (make-ind-Vec stx (parse-pie #'k) (parse-pie #'xs) (parse-pie #'m) (parse-pie #'b) (parse-pie #'s))]
    [(Either ~! L R)
     (make-Either stx (parse-pie #'L) (parse-pie #'R))]
    [(left ~! l)
     (make-left stx (parse-pie #'l))]
    [(right ~! r)
     (make-right stx (parse-pie #'r))]
    [(ind-Either ~! tgt mot l r)
     (make-ind-Either stx (parse-pie #'tgt) (parse-pie #'mot) (parse-pie #'l) (parse-pie #'r))]
    [(~describe "TODO" TODO)
     (make-TODO stx)]
    [(~describe "function application"
                ((~describe "function" rator)
                 (~describe "first argument" rand0)
                 (~describe "more arguments" rand) ...))
     (make-ap stx (parse-pie #'rator) (parse-pie #'rand0) (map parse-pie (syntax->list #'(rand ...))))]))

(define (parse-pie-decl stx)
  (syntax-parse stx
    #:datum-literals (claim define check-same)
    [(~describe "claim"
                (claim ~!
                       (~describe "name" x:pie-id)
                       (~describe "type" type)))
     `(claim ,(syntax->datum #'x)
             ,(syntax->srcloc #'x)
             ,(parse-pie #'type))]
    [(~describe "definition"
                (define ~!
                  (~describe "name" x:pie-id)
                  (~describe "definiens" e)))
     `(definition
        ,(syntax->datum #'x)
        ,(syntax->srcloc #'x)
        ,(parse-pie #'e))]
    [(~describe "sameness check"
                (check-same ~!
                            (~describe "type" type)
                            (~describe (format "first ~a" (syntax->datum #'type)) e1)
                            (~describe (format "second ~a" (syntax->datum #'type)) e2)))
     `(check-same ,(syntax->srcloc stx)
                  ,(parse-pie #'type)
                  ,(parse-pie #'e1)
                  ,(parse-pie #'e2))]
    [(~describe "expression" e)
     `(expression ,(parse-pie #'e))]))


(define-for-syntax (add-disappeared stx id)
  (syntax-property stx
                   'disappeared-use
                   (syntax-property (syntax-local-introduce id)
                                    'original-for-check-syntax
                                    #t)))

(define-syntax (pie->binders expr)
  (define stx
    (syntax-parse expr
      [(_ expr) #'expr]))
  (syntax-parse stx
    #:datum-literals (U
                      Nat zero add1
                      which-Nat iter-Nat rec-Nat ind-Nat
                      → -> Pi Π ∏ the lambda λ  Atom quote
                      cons car cdr Sigma Σ Pair
                      Trivial sole
                      List :: nil ind-List rec-List
                      Absurd ind-Absurd
                      = same replace symm trans cong ind-=
                      head tail Vec vec:: vecnil ind-Vec
                      Either left right ind-Either
                      TODO)
    [U
     (add-disappeared (syntax/loc stx kw:U)
                      stx)]
    [Nat
     (add-disappeared (syntax/loc stx kw:Nat)
                      stx)]
    [(→ ~! A B C ...)
     (with-syntax ([A* #'(pie->binders A)]
                   [B* #'(pie->binders B)]
                   [(C* ...) #'((pie->binders C) ...)]
                   [arr (syntax/loc (car (syntax-e stx)) kw:→)])
       (add-disappeared (syntax/loc stx (arr A* B* C* ...))
                        (car (syntax-e stx))))]
    [(-> ~! A B C ...)
     (with-syntax ([A* #'(pie->binders A)]
                   [B* #'(pie->binders B)]
                   [(C* ...) #'((pie->binders C) ...)]
                   [arr (syntax/loc (car (syntax-e stx)) kw:->)])
       (add-disappeared (syntax/loc stx (arr A* B* C* ...))
                        (car (syntax-e stx))))]
    [zero
     (add-disappeared (syntax/loc stx kw:zero)
                      stx)]
    [(add1 ~! n)
     (with-syntax ([n* #'(pie->binders n)]
                   [succ (syntax/loc (car (syntax-e stx)) kw:add1)])
       (add-disappeared (syntax/loc stx (succ n*))
                        (car (syntax-e stx))))]
    [(lambda ~! (x0:id x:id ...) b)
     (with-syntax ([lam/loc (syntax/loc (car (syntax-e stx)) kw:lambda)]
                   [b/bindings #'(pie->binders b)])
       (add-disappeared (syntax/loc stx
                          (void lam/loc
                                (let* ([x0 (void)] [x (void)] ...)
                                  b/bindings)))
                        (car (syntax-e stx))))]
    [(λ ~! (x0:id x:id ...) b)
     (with-syntax ([lam/loc (syntax/loc (car (syntax-e stx)) kw:λ)]
                   [b/bindings #'(pie->binders b)])
       (add-disappeared (syntax/loc stx
                          (void lam/loc
                                (let* ([x0 (void)] [x (void)] ...)
                                  b/bindings)))
                        (car (syntax-e stx))))]
    [(Pi ~! ((x0:id A0) (x:id A) ...) B)
     (with-syntax ([sig/loc (syntax/loc (car (syntax-e stx)) kw:Pi)]
                   [A0* #'(pie->binders A0)]
                   [(A* ...) #'((pie->binders A) ...)]
                   [B* #'(pie->binders B)])
       (add-disappeared (syntax/loc stx
                          (void sig/loc (let* ([x0 A0*] [x A*] ...) B*)))
                        (car (syntax-e stx))))]
    [(Π ~! ((x0:id A0) (x:id A) ...) B)
     (with-syntax ([sig/loc (syntax/loc (car (syntax-e stx)) kw:Π)]
                   [A0* #'(pie->binders A0)]
                   [(A* ...) #'((pie->binders A) ...)]
                   [B* #'(pie->binders B)])
       (add-disappeared (syntax/loc stx
                          (void sig/loc (let* ([x0 A0*] [x A*] ...) B*)))
                        (car (syntax-e stx))))]
    [(∏ ~! ((x0:id A0) (x:id A) ...) B)
     (with-syntax ([sig/loc (syntax/loc (car (syntax-e stx)) kw:∏)]
                   [A0* #'(pie->binders A0)]
                   [(A* ...) #'((pie->binders A) ...)]
                   [B* #'(pie->binders B)])
       (add-disappeared (syntax/loc stx
                          (void sig/loc (let* ([x0 A0*] [x A*] ...) B*)))
                        (car (syntax-e stx))))]
    [(Sigma ~! ((x0:id A0) (x:id A) ...) B)
     (with-syntax ([sig/loc (syntax/loc (car (syntax-e stx)) kw:Sigma)]
                   [A0* #'(pie->binders A0)]
                   [(A* ...) #'((pie->binders A) ...)]
                   [B* #'(pie->binders B)])
       (add-disappeared (syntax/loc stx
                          (void sig/loc (let* ([x0 A0*] [x A*] ...) B*)))
                        (car (syntax-e stx))))]
    [(Σ ~! ((x0:id A0) (x:id A) ...) B)
     (with-syntax ([sig/loc (syntax/loc (car (syntax-e stx)) kw:Σ)]
                   [A0* #'(pie->binders A0)]
                   [(A* ...) #'((pie->binders A) ...)]
                   [B* #'(pie->binders B)])
       (add-disappeared (syntax/loc stx (void sig/loc (let* ([x0 A0*] [x A*] ...) B*)))
                        (car (syntax-e stx))))]
    [(Pair ~! A D)
     (with-syntax ([A* #'(pie->binders A)]
                   [D* #'(pie->binders D)]
                   [pair/loc (syntax/loc (car (syntax-e stx)) kw:Pair)])
       (add-disappeared (syntax/loc stx (void pair/loc A* D*))
                        (car (syntax-e stx))))]
    [(cons ~! a d)
     (with-syntax ([a* #'(pie->binders a)]
                   [d* #'(pie->binders d)]
                   [cons/loc (syntax/loc (car (syntax-e stx)) kw:cons)])
       (add-disappeared (syntax/loc stx (void cons/loc a* d*))
                        (car (syntax-e stx))))]
    [(car ~! p)
     (with-syntax ([p* #'(pie->binders p)]
                   [car/loc (syntax/loc (car (syntax-e stx)) kw:car)])
       (add-disappeared (syntax/loc stx (void car/loc p*))
                        (car (syntax-e stx))))]
    [(cdr ~! p)
     (with-syntax ([p* #'(pie->binders p)]
                   [cdr/loc (syntax/loc (car (syntax-e stx)) kw:cdr)])
       (add-disappeared (syntax/loc stx (void cdr/loc p*))
                        (car (syntax-e stx))))]
    [(the ~! t e)
     (with-syntax ([t* #'(pie->binders t)]
                   [e* #'(pie->binders e)]
                   [the/loc (syntax/loc (car (syntax-e stx)) kw:the)])
       (add-disappeared (syntax/loc stx (void the/loc t* e*))
                        (car (syntax-e stx))))]
    [(which-Nat ~! tgt b s)
     (with-syntax ([tgt* #'(pie->binders tgt)]
                   [b* #'(pie->binders b)]
                   [s* #'(pie->binders s)]
                   [which-Nat/loc (syntax/loc (car (syntax-e stx)) kw:which-Nat)])
       (add-disappeared (syntax/loc stx (void which-Nat/loc tgt* b* s*))
                        (car (syntax-e stx))))]
    [(rec-Nat ~! tgt b s)
     (with-syntax ([tgt* #'(pie->binders tgt)]
                   [b* #'(pie->binders b)]
                   [s* #'(pie->binders s)]
                   [rec-Nat/loc (syntax/loc (car (syntax-e stx)) kw:rec-Nat)])
       (add-disappeared (syntax/loc stx (void rec-Nat/loc tgt* b* s*))
                        (car (syntax-e stx))))]
    [(iter-Nat ~! tgt b s)
     (with-syntax ([tgt* #'(pie->binders tgt)]
                   [b* #'(pie->binders b)]
                   [s* #'(pie->binders s)]
                   [iter-Nat/loc (syntax/loc (car (syntax-e stx)) kw:iter-Nat)])
       (add-disappeared (syntax/loc stx (void iter-Nat/loc tgt* b* s*))
                        (car (syntax-e stx))))]
    [(ind-Nat ~! tgt mot b s)
     (with-syntax ([tgt* #'(pie->binders tgt)]
                   [mot* #'(pie->binders mot)]
                   [b* #'(pie->binders b)]
                   [s* #'(pie->binders s)]
                   [ind-Nat/loc (syntax/loc (car (syntax-e stx)) kw:ind-Nat)])
       (add-disappeared (syntax/loc stx (void ind-Nat/loc tgt* mot* b* s*))
                        (car (syntax-e stx))))]
    [Atom
     (add-disappeared (syntax/loc stx kw:Atom)
                      stx)]
    [(quote ~! a:id)
     (with-syntax ([quote/loc (syntax/loc (car (syntax-e stx)) kw:quote)])
       (add-disappeared (syntax/loc stx (void quote/loc 'a))
                        (car (syntax-e stx))))]
    [Trivial
     (add-disappeared (syntax/loc stx kw:Trivial) stx)]
    [sole
     (add-disappeared (syntax/loc stx kw:sole)
                      stx)]
    [(List ~! E)
     (with-syntax ([E* #'(pie->binders E)]
                   [List/loc (syntax/loc (car (syntax-e stx)) kw:List)])
       (add-disappeared (syntax/loc stx (void List/loc E*))
                        (car (syntax-e stx))))]
    [nil
     (add-disappeared (syntax/loc stx kw:nil)
                      stx)]
    [(:: ~! a d)
     (with-syntax ([a* #'(pie->binders a)]
                   [d* #'(pie->binders d)]
                   [::/loc (syntax/loc (car (syntax-e stx)) kw:::)])
       (add-disappeared (syntax/loc stx (void ::/loc a* d*))
                        (car (syntax-e stx))))]
    [(ind-List ~! tgt mot b s)
     (with-syntax ([tgt* #'(pie->binders tgt)]
                   [mot* #'(pie->binders mot)]
                   [b* #'(pie->binders b)]
                   [s* #'(pie->binders s)]
                   [ind-List/loc (syntax/loc (car (syntax-e stx)) kw:ind-List)])
       (add-disappeared (syntax/loc stx (void ind-List/loc tgt* mot* b* s*))
                        (car (syntax-e stx))))]
    [(rec-List ~! tgt b s)
     (with-syntax ([tgt* #'(pie->binders tgt)]
                   [b* #'(pie->binders b)]
                   [s* #'(pie->binders s)]
                   [rec-List/loc (syntax/loc (car (syntax-e stx)) kw:rec-List)])
       (add-disappeared (syntax/loc stx (void rec-List/loc tgt*  b* s*))
                        (car (syntax-e stx))))]
    [x:pie-id
     stx]
    [Absurd
     (add-disappeared (syntax/loc stx kw:Absurd) stx)]
    [(ind-Absurd ~! tgt mot)
     (with-syntax ([tgt* #'(pie->binders tgt)]
                   [mot* #'(pie->binders mot)]
                   [ind-Absurd/loc (syntax/loc (car (syntax-e stx)) kw:ind-Absurd)])
       (add-disappeared (syntax/loc stx (void ind-Absurd/loc tgt* mot*))
                        (car (syntax-e stx))))]
    [n:nat
     (syntax/loc stx (void n))]
    [(= ~! A from to)
     (with-syntax ([A* #'(pie->binders A)]
                   [from* #'(pie->binders from)]
                   [to* #'(pie->binders to)]
                   [=/loc (syntax/loc (car (syntax-e stx)) kw:=)])
       (add-disappeared (syntax/loc stx (void =/loc A* from* to*))
                        (car (syntax-e stx))))]
    [(same ~! e)
     (with-syntax ([e* #'(pie->binders e)]
                   [same/loc (syntax/loc (car (syntax-e stx)) kw:same)])
       (add-disappeared (syntax/loc stx (void same/loc e*))
                        (car (syntax-e stx))))]
    [(replace ~! tgt mot b)
     (with-syntax ([tgt* #'(pie->binders tgt)]
                   [mot* #'(pie->binders mot)]
                   [b* #'(pie->binders b)]
                   [replace/loc (syntax/loc (car (syntax-e stx)) kw:replace)])
       (add-disappeared (syntax/loc stx (void replace/loc tgt* mot* b*))
                        (car (syntax-e stx))))]
    [(trans ~! a d)
     (with-syntax ([a* #'(pie->binders a)]
                   [d* #'(pie->binders d)]
                   [trans/loc (syntax/loc (car (syntax-e stx)) kw:trans)])
       (add-disappeared (syntax/loc stx (void trans/loc a* d*))
                        (car (syntax-e stx))))]
    [(cong ~! a d)
     (with-syntax ([a* #'(pie->binders a)]
                   [d* #'(pie->binders d)]
                   [cong/loc (syntax/loc (car (syntax-e stx)) kw:cong)])
       (add-disappeared (syntax/loc stx (void cong/loc a* d*))
                        (car (syntax-e stx))))]
    [(symm ~! p)
     (with-syntax ([p* #'(pie->binders p)]
                   [symm/loc (syntax/loc (car (syntax-e stx)) kw:symm)])
       (add-disappeared (syntax/loc stx (void symm/loc p*))
                        (car (syntax-e stx))))]
    [(ind-= ~! tgt mot base)
     (with-syntax ([tgt* #'(pie->binders tgt)]
                   [mot* #'(pie->binders mot)]
                   [base* #'(pie->binders base)]
                   [ind-=/loc (syntax/loc (car (syntax-e stx)) kw:ind-=)])
       (add-disappeared (syntax/loc stx (void ind-=/loc tgt* mot* base*))
                        (car (syntax-e stx))))]
    [(Vec ~! E len)
     (with-syntax ([E* #'(pie->binders E)]
                   [len* #'(pie->binders len)]
                   [Vec/loc (syntax/loc (car (syntax-e stx)) kw:Vec)])
       (add-disappeared (syntax/loc stx (void Vec/loc E* len*))
                        (car (syntax-e stx))))]
    [vecnil
     (add-disappeared (syntax/loc stx kw:vecnil)
                      stx)]
    [(vec:: ~! a d)
     (with-syntax ([a* #'(pie->binders a)]
                   [d* #'(pie->binders d)]
                   [vec::/loc (syntax/loc (car (syntax-e stx)) kw:vec::)])
       (add-disappeared (syntax/loc stx (void vec::/loc a* d*))
                        (car (syntax-e stx))))]
    [(head ~! p)
     (with-syntax ([p* #'(pie->binders p)]
                   [head/loc (syntax/loc (car (syntax-e stx)) kw:head)])
       (add-disappeared (syntax/loc stx (void head/loc p*))
                        (car (syntax-e stx))))]
    [(tail ~! p)
     (with-syntax ([p* #'(pie->binders p)]
                   [tail/loc (syntax/loc (car (syntax-e stx)) kw:tail)])
       (add-disappeared (syntax/loc stx (void tail/loc p*))
                        (car (syntax-e stx))))]
    [(ind-Vec ~! k tgt mot b s)
     (with-syntax ([k* #'(pie->binders k)]
                   [tgt* #'(pie->binders tgt)]
                   [mot* #'(pie->binders mot)]
                   [b* #'(pie->binders b)]
                   [s* #'(pie->binders s)]
                   [ind-Vec/loc (syntax/loc (car (syntax-e stx)) kw:ind-Vec)])
       (add-disappeared (syntax/loc stx (void ind-Vec/loc k* tgt* mot* b* s*))
                        (car (syntax-e stx))))]
    [(Either ~! L R)
     (with-syntax ([L* #'(pie->binders L)]
                   [R* #'(pie->binders R)]
                   [Either/loc (syntax/loc (car (syntax-e stx)) kw:Either)])
       (add-disappeared (syntax/loc stx (void Either/loc L* R*))
                        (car (syntax-e stx))))]
    [(left ~! p)
     (with-syntax ([p* #'(pie->binders p)]
                   [left/loc (syntax/loc (car (syntax-e stx)) kw:left)])
       (add-disappeared (syntax/loc stx (void left/loc p*))
                        (car (syntax-e stx))))]
    [(right ~! p)
     (with-syntax ([p* #'(pie->binders p)]
                   [right/loc (syntax/loc (car (syntax-e stx)) kw:right)])
       (add-disappeared (syntax/loc stx (void right/loc p*))
                        (car (syntax-e stx))))]
    [(ind-Either ~! tgt mot l r)
     (with-syntax ([tgt* #'(pie->binders tgt)]
                   [mot* #'(pie->binders mot)]
                   [l* #'(pie->binders l)]
                   [r* #'(pie->binders r)]
                   [ind-Either/loc (syntax/loc (car (syntax-e stx)) kw:ind-Either)])
       (add-disappeared (syntax/loc stx (void ind-Either/loc tgt* mot* l* r*))
                        (car (syntax-e stx))))]
    [(~describe "TODO" TODO)
     (add-disappeared (syntax/loc stx kw:TODO)
                      stx)]
    [(~describe "application" (rator rand0 rand ...))
     (with-syntax ([rator* #'(pie->binders rator)]
                   [rand0* #'(pie->binders rand0)]
                   [(rand* ...) #'((pie->binders rand) ...)])
       (syntax/loc stx (void rator* rand0* rand* ...)))]
    [_ #'(void)]))

(define-syntax (pie-decl->binders decl)
  (define stx
    (syntax-parse decl
      [(_ decl) #'decl]))
  (syntax-parse stx
    #:datum-literals (claim define check-same)
    [(~describe "claim"
                (claim ~!
                       (~describe "name" x:id)
                       (~describe "type" type)))
     (with-syntax ([claim/loc (syntax/loc (car (syntax-e stx)) kw:claim)]
                   [claim-var (format-id #'x "internal-claim-binding-~a" #'x #:source #'x)]
                   [claim-ty #'(pie->binders type)])
       (syntax-property
        (add-disappeared (syntax/loc stx
                           (define claim-var (void claim/loc claim-ty)))
                         (car (syntax-e stx)))
        'disappeared-binding (syntax-local-introduce #'x)))]
    [(~describe "definition"
                (define ~!
                  (~describe "name" x:id)
                  (~describe "definiens" e)))
     (with-syntax ([define/loc (syntax/loc (car (syntax-e stx)) kw:define)]
                   [claim-var (format-id #'x "internal-claim-binding-~a" #'x)]
                   [define-e #'(pie->binders e)])
       (add-disappeared (add-disappeared
                         (syntax/loc stx
                           (define x (void define/loc claim-var define-e)))
                         (car (syntax-e stx)))
                        #'x))]
    [(~describe "sameness check"
                (check-same ~!
                            (~describe "type" type)
                            (~describe (format "first ~a" (syntax->datum #'type)) e1)
                            (~describe (format "second ~a" (syntax->datum #'type)) e2)))
     (with-syntax ([check-same/loc (syntax/loc (car (syntax-e stx)) kw:check-same)]
                   [type* #'(pie->binders type)]
                   [e1* #'(pie->binders e1)]
                   [e2* #'(pie->binders e2)])
       (add-disappeared (syntax/loc stx (void check-same/loc type* e1* e2*)) (car (syntax-e stx))))]
    [(~describe "expression" e)
     #'(pie->binders e)]))


