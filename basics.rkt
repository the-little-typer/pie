#lang typed/racket/base

;;; basics.rkt
;;;
;;; This file contains preliminary definitions that are needed in
;;; the rest of the system, including datatypes for ASTs, values,
;;; contexts, states, etc.

(require (for-syntax racket/base syntax/parse) racket/match
         "fresh.rkt")
(provide (all-defined-out)
         (for-syntax (all-defined-out))
         Precise-Loc
         location?
         syntax->location
         location->srcloc
         Srcloc)


(define-type Srcloc (List String Integer Integer Integer Integer))

(require/typed "locations.rkt"
  [#:opaque Precise-Loc location?]
  [location-for-info? (-> Precise-Loc Boolean)]
  [syntax->location (-> Syntax Precise-Loc)]
  [location->srcloc (-> Precise-Loc Srcloc)]
  [not-for-info (-> Precise-Loc Precise-Loc)])


;;; Note that Loc is used for the equality of TODO that comes out of read-back, so
;;; it should not be a trivial value.
(define-type Loc Precise-Loc)

;%%%%%DPF Portland+2 Shouldn't Pie Keywords include ind-Sigma (?)  

(define-type Pie-Keyword
  (U 'U
     'Nat 'zero 'add1 'which-Nat 'iter-Nat 'rec-Nat 'ind-Nat
     '-> '→ 'Π 'λ 'Pi 'lambda
     'quote 'Atom
     'car 'cdr 'cons 'Σ 'Sigma 'Pair
     'Trivial 'sole
     'List ':: 'nil 'rec-List 'ind-List
     'Absurd 'ind-Absurd
     '= 'same 'replace 'trans 'cong 'symm 'ind-=
     'Vec 'vecnil 'vec:: 'head 'tail 'ind-Vec
     'Either 'left 'right 'ind-Either
     'TODO 'the))

;;; Abstract syntax of high-level programs


(struct @ ([loc : Loc]
           [stx : Src-Stx])
  #:transparent
  #:type-name Src)

(: src-loc (-> Src Loc))
(define src-loc @-loc)

(: src-stx (-> Src Src-Stx))
(define src-stx @-stx)

(: src? (-> Any Boolean : Src))
(define src? @?)

(struct binder ([loc : Loc] [var : Symbol]) #:transparent #:type-name Binding-Site)

(define-type Typed-Binder
  (List Binding-Site Src))

(define-type Src-Stx
  (U (List 'the Src Src)
     'U
     'Nat
     'zero
     Symbol
     'Atom
     (List 'quote Symbol)
     (List 'add1 Src)
     (List 'which-Nat Src Src Src)
     (List 'iter-Nat Src Src Src)
     (List 'rec-Nat Src Src Src)
     (List 'ind-Nat Src Src Src Src)
     (List* '-> Src Src (Listof Src))
     (List 'Π (List* Typed-Binder (Listof Typed-Binder)) Src)
     (List 'λ (List* Binding-Site (Listof Binding-Site)) Src)
     (List 'Σ (List* Typed-Binder (Listof Typed-Binder)) Src)
     (List 'Pair Src Src)
     (List 'cons Src Src)
     (List 'car Src)
     (List 'cdr Src)
     'Trivial
     'sole
     'nil
     Natural
     (List ':: Src Src)
     (List 'List Src)
     (List 'rec-List Src Src Src)
     (List 'ind-List Src Src Src Src)
     'Absurd
     (List 'ind-Absurd Src Src)
     (List '= Src Src Src)
     (List 'same Src)
     (List 'replace Src Src Src)
     (List 'trans Src Src)
     (List 'cong Src Src)
     (List 'symm Src)
     (List 'ind-= Src Src Src)
     (List 'Vec Src Src)
     'vecnil
     (List 'vec:: Src Src)
     (List 'head Src)
     (List 'tail Src)
     (List 'ind-Vec Src Src Src Src Src)
     (List 'Either Src Src)
     (List 'left Src)
     (List 'right Src)
     (List 'ind-Either Src Src Src Src)
     'TODO
     (List* Src Src (Listof Src))))



(define-type Core
  (U (List 'the Core Core)
     'U
     'Nat
     'zero
     Symbol
     (List 'add1 Core)
     (List 'which-Nat Core (List 'the Core Core) Core)
     (List 'iter-Nat Core (List 'the Core Core) Core)
     (List 'rec-Nat Core (List 'the Core Core) Core)
     (List 'ind-Nat Core Core Core Core)
     (List 'Π (List (List Symbol Core)) Core)
     (List 'λ (List Symbol) Core)
     'Atom
     (List 'quote Symbol)
     (List 'Σ (List (List Symbol Core)) Core)
     (List 'cons Core Core)
     (List 'car Core)
     (List 'cdr Core)
     (List ':: Core Core)
     'nil
     (List 'List Core)
     (List 'rec-List Core (List 'the Core Core) Core)
     (List 'ind-List Core Core Core Core)
     'Absurd
     (List 'ind-Absurd Core Core)
     (List '= Core Core Core)
     (List 'same Core)
     (List 'replace Core Core Core)
     (List 'trans Core Core)
     (List 'cong Core Core Core) ;; Extra expr is type found through synth
     (List 'symm Core)
     (List 'ind-= Core Core Core)
     (List 'Vec Core Core)
     (List 'vec:: Core Core)
     'vecnil
     (List 'head Core)
     (List 'tail Core)
     (List 'ind-Vec Core Core Core Core Core)
     (List 'Either Core Core)
     (List 'left Core)
     (List 'right Core)
     (List 'ind-Either Core Core Core Core)
     (List 'TODO Srcloc Core)
     (List Core Core)))

;; Laziness is implemented by allowing values to be a closure that
;; does not bind a variable.
(struct DELAY ([env : Env] [expr : Core]) #:transparent)

(struct QUOTE ([name : Symbol]) #:transparent)
(struct ADD1 ([smaller : Value]) #:transparent)
(struct PI ([arg-name : Symbol]
            [arg-type : Value]
            [result-type : Closure])
  #:transparent)
(struct LAM ([arg-name : Symbol] [body : Closure]) #:transparent)
(struct SIGMA ([car-name : Symbol]
               [car-type : Value]
               [cdr-type : Closure])
  #:transparent)
(struct CONS ([car : Value] [cdr : Value]) #:transparent)
(struct LIST:: ([head : Value] [tail : Value]) #:transparent)
(struct LIST ([entry-type : Value]) #:transparent)
(struct EQUAL ([type : Value] [from : Value] [to : Value])
  #:transparent)
(struct SAME ([value : Value]) #:transparent)
(struct VEC ([entry-type : Value] [length : Value]) #:transparent)
(struct VEC:: ([head : Value] [tail : Value]) #:transparent)
(struct EITHER ([left-type : Value] [right-type : Value]) #:transparent)
(struct LEFT ([value : Value]) #:transparent)
(struct RIGHT ([value : Value]) #:transparent)
(struct NEU ([type : Value] [neutral : Neutral]) #:transparent)
(define-type Value
  (U 'UNIVERSE
     'NAT 'ZERO ADD1
     QUOTE 'ATOM
     PI LAM
     SIGMA CONS
     'TRIVIAL 'SOLE
     LIST LIST:: 'NIL
     'ABSURD
     EQUAL SAME
     VEC 'VECNIL VEC::
     EITHER LEFT RIGHT
     NEU
     DELAY))

(struct N-var ([name : Symbol]) #:transparent)
(struct N-TODO ([where : Srcloc] [type : Value]) #:transparent)
(struct N-which-Nat ([target : Neutral] [base : Norm] [step : Norm]) #:transparent)
(struct N-iter-Nat ([target : Neutral] [base : Norm] [step : Norm]) #:transparent)
(struct N-rec-Nat ([target : Neutral] [base : Norm] [step : Norm]) #:transparent)
(struct N-ind-Nat ([target : Neutral]
                   [motive : Norm]
                   [base : Norm]
                   [step : Norm])
  #:transparent)
(struct N-car ([target : Neutral]) #:transparent)
(struct N-cdr ([target : Neutral]) #:transparent)
(struct N-rec-List ([target : Neutral] [base : Norm] [step : Norm]) #:transparent)
(struct N-ind-List ([target : Neutral]
                    [motive : Norm]
                    [base : Norm]
                    [step : Norm])
  #:transparent)
(struct N-ind-Absurd ([target : Neutral] [motive : Norm]) #:transparent)
(struct N-replace ([target : Neutral] [motive : Norm] [base : Norm]) #:transparent)
(struct N-trans1 ([target1 : Neutral] [target2 : Norm]) #:transparent)
(struct N-trans2 ([target1 : Norm] [target2 : Neutral]) #:transparent)
(struct N-trans12 ([target1 : Neutral] [target2 : Neutral]) #:transparent)
;; function contains enough to get back res type, so only two fields here
(struct N-cong ([target : Neutral] [function : Norm]) #:transparent)
(struct N-symm ([target : Neutral]) #:transparent)
(struct N-ind-= ([target : Neutral] [motive : Norm] [base : Norm]) #:transparent)
(struct N-head ([target : Neutral]) #:transparent)
(struct N-tail ([target : Neutral]) #:transparent)
(struct N-ind-Vec1 ([target1 : Neutral]
                    [target2 : Norm]
                    [motive : Norm]
                    [base : Norm]
                    [step : Norm])
  #:transparent)
(struct N-ind-Vec2 ([target1 : Norm]
                    [target2 : Neutral]
                    [motive : Norm]
                    [base : Norm]
                    [step : Norm])
  #:transparent)
(struct N-ind-Vec12 ([target1 : Neutral]
                    [target2 : Neutral]
                    [motive : Norm]
                    [base : Norm]
                    [step : Norm])
  #:transparent)
(struct N-ind-Either ([target : Neutral]
                      [motive : Norm]
                      [base-left : Norm]
                      [base-right : Norm])
  #:transparent)
(struct N-ap ([rator : Neutral] [rand : Norm]) #:transparent)

(define-type Neutral
  (U N-var N-TODO
     N-which-Nat N-iter-Nat N-rec-Nat N-ind-Nat
     N-car N-cdr
     N-rec-List N-ind-List
     N-ind-Absurd
     N-replace N-trans1 N-trans2 N-trans12 N-cong N-symm N-ind-=
     N-head N-tail N-ind-Vec1 N-ind-Vec2 N-ind-Vec12
     N-ind-Either
     N-ap))

(define-predicate Neutral? Neutral)

(struct THE ([type : Value] [value : Value]) #:transparent #:type-name Norm)

(define-predicate Norm? Norm)

(define-type Message
  (Listof (U String Core)))

(define-type (Perhaps α)
  (U (go α) stop))

(struct (α) go ([result : α]) #:transparent)
(struct stop ([where : Loc] [message : Message]) #:transparent)

(define-syntax-rule (define-here-and-for-syntax what impl)
  (begin (define what impl)
         (begin-for-syntax (define what impl))))

(: var-name? (-> Symbol Boolean :
                 #:+ (! Pie-Keyword)
                 #:- Pie-Keyword))
(define-here-and-for-syntax (var-name? x)
  (not (or (eqv? x 'U) (eqv? x 'Nat) (eqv? x 'zero)
           (eqv? x 'add1) (eqv? x 'which-Nat) (eqv? x 'ind-Nat)
           (eqv? x 'rec-Nat) (eqv? x 'iter-Nat)
           (eqv? x '->) (eqv? x '→) (eqv? x 'Π) (eqv? x 'Pi) (eqv? x 'λ) (eqv? x 'lambda)
           (eqv? x 'quote) (eqv? x 'Atom) (eqv? x 'Σ) (eqv? x 'Sigma) (eqv? x 'Pair)
           (eqv? x 'cons) (eqv? x 'car) (eqv? x 'cdr)
           (eqv? x 'Trivial) (eqv? x 'sole)
           (eqv? x '::) (eqv? x 'nil) (eqv? x 'List)
           (eqv? x 'rec-List) (eqv? x 'ind-List)
           (eqv? x 'Absurd) (eqv? x 'ind-Absurd)
           (eqv? x '=) (eqv? x 'same) (eqv? x 'replace)
           (eqv? x 'symm) (eqv? x 'trans) (eqv? x 'cong) (eqv? x 'ind-=)
           (eqv? x 'Vec) (eqv? x 'vec::) (eqv? x 'vecnil)
           (eqv? x 'head) (eqv? x 'tail) (eqv? x 'ind-Vec)
           (eqv? x 'Either) (eqv? x 'left) (eqv? x 'right)
           (eqv? x 'ind-Either) (eqv? x 'the)
           (eqv? x 'TODO))))


(define-syntax (go-on stx)
  (syntax-parse stx
    [(go-on () e) (syntax/loc stx e)]
    [(go-on ((p0 b0) (p b) ...) e)
     (syntax/loc stx
       (match b0
         [(go p0) (go-on ((p b) ...) e)]
         [(stop where msg) (stop where msg)]))]))



(define-type Binder (U Def Free Claim))
(define-type Claim claim)
(struct claim ([type : Value]) #:transparent)
(struct def ([type : Value] [value : Value]) #:transparent #:type-name Def)
(struct free ([type : Value]) #:transparent #:type-name Free)

(: binder-type (-> Binder Value))
(define (binder-type b)
  (match b
    [(claim tv) tv]
    [(def tv v) tv]
    [(free tv) tv]))

(define-type Ctx
  (Listof (Pair Symbol Binder)))

(define-type Serializable-Ctx
  (Listof (List Symbol (U (List 'free Core)
                          (List 'def Core Core)
                          (List 'claim Core)))))

(define-predicate serializable-ctx? Serializable-Ctx)

(define-type Env
  (Listof (Pair Symbol Value)))

(: ctx->env (-> Ctx Env))
(define (ctx->env Γ)
  (match Γ
    [(cons (cons x (def tv v)) Γ-next)
     (cons (cons x v)
           (ctx->env Γ-next))]
    [(cons (cons x (free tv)) Γ-next)
     (cons (cons x (NEU tv (N-var x)))
           (ctx->env Γ-next))]
    [(cons (cons x (claim tv)) Γ-next)
     (ctx->env Γ-next)]
    ['() '()]))

(define-type Closure (U FO-CLOS HO-CLOS))
(struct FO-CLOS ([env : Env] [var : Symbol] [expr : Core]) #:transparent)
(struct HO-CLOS ([proc : (-> Value Value)]) #:transparent)


(: init-ctx Ctx)
(define init-ctx '())

(: bind-free (-> Ctx Symbol Value Ctx))
(define (bind-free Γ x tv)
  (if (assv x Γ)
      (error 'bind-free "~a is already bound in ~a" x Γ)
      (cons (cons x (free tv)) Γ)))

(: bind-val (-> Ctx Symbol Value Value Ctx))
(define (bind-val Γ x tv v)
  (cons (cons x (def tv v)) Γ))

(: extend-env (-> Env Symbol Value Env))
(define (extend-env ρ x v) (cons (cons x v) ρ))

(: unfold-defs? (Parameterof Boolean))
(define unfold-defs? (make-parameter #t))

(: var-val (-> Env Symbol Value))
(define (var-val ρ x)
  (match (assv x ρ)
    [(cons y v) v]
    [#f (error (format "Variable ~a not in\n\tρ: ~a\n" x ρ))]))

(: var-type (-> Ctx Loc Symbol (Perhaps Value)))
(define (var-type Γ where x)
  (match Γ
    ['() (stop where `("Unknown variable" ,x))]
    [(cons (cons y (claim tv)) Γ-next)
     (var-type Γ-next where x)]
    [(cons (cons y b) Γ-next)
     (if (eqv? x y)
         (go (binder-type b))
         (var-type Γ-next where x))]))

(: names-only (-> Ctx (Listof Symbol)))
(define (names-only Γ)
  (cond
    [(null? Γ) '()]
    [else (cons (car (car Γ)) (names-only (cdr Γ)))]))

(: fresh (-> Ctx Symbol Symbol))
(define (fresh Γ x)
  (freshen (names-only Γ) x))

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


