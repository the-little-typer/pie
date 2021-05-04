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


;;; Source locations

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


;;; Keywords

(define-type Pie-Keyword
  (U 'U
     'Nat 'zero 'add1 'which-Nat 'iter-Nat 'rec-Nat 'ind-Nat
     '-> '→ 'Π 'λ 'Pi '∏ 'lambda
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

;; @ associates a source location with a Pie expression or
;; declaration. This allows the implementation to report give precise,
;; helpful feedback.
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


;;; Pie expressions consist of a source location attached by @ to an
;;; S-expression that follows the structure defined in The Little
;;; Typer. Each sub-expression also has a source location, so they are
;;; Src rather than Src-Stx.
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

;; Core Pie expressions are the result of type checking (elaborating)
;; an expression written in Pie. They do not have source positions,
;; because they by definition are not written by a user of the
;; implementation.
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


;;; Values

;; In order to type check Pie, it is necessary to find the normal
;; forms of expressions and compare them with each other. The normal
;; form of an expression is determined by its type - types that have
;; η-rules (such as Π, Σ, Trivial, and Absurd) impose requirements on
;; the normal form. For instance, every normal function has λ at the
;; top, and every normal pair has cons at the top.

;; Finding normal forms has two steps: first, programs are evaluated,
;; much as they are with the Scheme interpreter at the end of The
;; Little Schemer. Then, these values are "read back" into the syntax
;; of their normal forms. This happens in normalize.rkt. This file
;; defines the values that expressions can have. Structures or symbols
;; that represent values are written in ALL-CAPS.

;; Laziness is implemented by allowing values to be a closure that
;; does not bind a variable. It is described in normalize.rkt (search
;; for "Call-by-need").
(struct DELAY-CLOS ([env : Env] [expr : Core]) #:transparent)
(struct DELAY ([val : (Boxof (U DELAY-CLOS Value))]) #:transparent)

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


;; Neutral expressions are represented by structs that ensure that no
;; non-neutral expressions can be represented.

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

;; Normal forms consist of syntax that is produced by read-back,
;; following the type. This structure contains a type value and a
;; value described by the type, so that read-back can later be applied
;; to it.
(struct THE ([type : Value] [value : Value]) #:transparent #:type-name Norm)

(define-predicate Norm? Norm)


;;; Error handling

;; Messages to be shown to the user contain a mix of text (represented
;; as strings) and expressions (represented as Core Pie expressions).
(define-type Message
  (Listof (U String Core)))

;; The result of an operation that can fail, such as type checking, is
;; represented using either the stop or the go structures.
(define-type (Perhaps α)
  (U (go α) stop))

;; A successful result
(struct (α) go ([result : α]) #:transparent)

;; An error message
(struct stop ([where : Loc] [message : Message]) #:transparent)

;; go-on is very much like let*. The difference is that if any of the
;; values bound to variables in it are stop, then the entire
;; expression becomes that first stop. Otherwise, the variables are
;; bound to the contents of each go.
(define-syntax (go-on stx)
  (syntax-parse stx
    [(go-on () e) (syntax/loc stx e)]
    [(go-on ((p0 b0) (p b) ...) e)
     (syntax/loc stx
       (match b0
         [(go p0) (go-on ((p b) ...) e)]
         [(stop where msg) (stop where msg)]))]))


;;; Recognizing variable names

;; This macro causes a name to be defined both for Racket macros and
;; for use in ordinary Racket programs. In Racket, these are
;; separated.
;;
;; Variable name recognition is needed in Racket macros in order to
;; parse Pie into the Src type, and it is needed in ordinary programs
;; in order to implement the type checker.
(define-syntax-rule (define-here-and-for-syntax what impl)
  (begin (define what impl)
         (begin-for-syntax (define what impl))))

;; The type of var-name? guarantees that the implementation will
;; always accept symbols that are not Pie keywords, and never accept
;; those that are.
(: var-name? (-> Symbol Boolean :
                 #:+ (! Pie-Keyword)
                 #:- Pie-Keyword))
(define-here-and-for-syntax (var-name? x)
  (not (or (eqv? x 'U) (eqv? x 'Nat) (eqv? x 'zero)
           (eqv? x 'add1) (eqv? x 'which-Nat) (eqv? x 'ind-Nat)
           (eqv? x 'rec-Nat) (eqv? x 'iter-Nat)
           (eqv? x '->) (eqv? x '→) (eqv? x 'Π) (eqv? x 'Pi) (eqv? x '∏) (eqv? x 'λ) (eqv? x 'lambda)
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




;;; Contexts

;; A context maps free variable names to binders.
(define-type Ctx
  (Listof (Pair Symbol Binder)))


;; There are three kinds of binders: a free binder represents a free
;; variable, that was bound in some larger context by λ, Π, or Σ. A
;; def binder represents a name bound by define. A claim binder
;; doesn't actually bind a name; however, it reserves the name for
;; later definition with define and records the type that will be
;; used.
(define-type Binder (U Def Free Claim))
(define-type Claim claim)
(struct claim ([type : Value]) #:transparent)
(struct def ([type : Value] [value : Value]) #:transparent #:type-name Def)
(struct free ([type : Value]) #:transparent #:type-name Free)


;; To find the type of a variable in a context, find the closest
;; non-claim binder and extract its type.
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

(: binder-type (-> Binder Value))
(define (binder-type b)
  (match b
    [(claim tv) tv]
    [(def tv v) tv]
    [(free tv) tv]))

;; The starting context is empty.
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


;; For informationa bout serializable contexts, see the comments in
;; normalize.rkt.
(define-type Serializable-Ctx
  (Listof (List Symbol (U (List 'free Core)
                          (List 'def Core Core)
                          (List 'claim Core)))))

(define-predicate serializable-ctx? Serializable-Ctx)




;;; Run-time environments

;; A run-time environment associates a value with each variable.
(define-type Env
  (Listof (Pair Symbol Value)))

;; When type checking Pie, it is sometimes necessary to find the
;; normal form of an expression that has free variables. These free
;; variables are described in the type checking context. The value
;; associated with each free variable should be itself - a neutral
;; expression. ctx->env converts a context into an environment by
;; assigning a neutral expression to each variable.
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

;; Extend an environment with a value for a new variable.
(: extend-env (-> Env Symbol Value Env))
(define (extend-env ρ x v) (cons (cons x v) ρ))

;; To find the value of a variable in an environment, look it up in
;; the usual Lisp way using assv.
(: var-val (-> Env Symbol Value))
(define (var-val ρ x)
  (match (assv x ρ)
    [(cons y v) v]
    [#f (error (format "Variable ~a not in\n\tρ: ~a\n" x ρ))]))



;;; Closures

;; There are two kinds of closures: first-order closures and
;; higher-order closures. They are used for different purposes in
;; Pie. It would be possible to have only one representation, but they
;; are good for different things, so both are included. See
;; val-of-closure in normalize.rkt for how to find the value of a
;; closure, given the value for its free variable.
(define-type Closure (U FO-CLOS HO-CLOS))

;; First-order closures, which are a pair of an environment an an
;; expression whose free variables are given values by the
;; environment, are used for most closures in Pie. They are easier to
;; debug, because their contents are visible rather than being part of
;; a compiled Racket function. On the other hand, they are more
;; difficult to construct out of values, because it would be necessary
;; to first read the values back into Core Pie syntax.
(struct FO-CLOS ([env : Env] [var : Symbol] [expr : Core]) #:transparent)

;; Higher-order closures re-used Racket's built-in notion of
;; closure. They are more convenient when constructing closures from
;; existing values, which happens both during type checking, where
;; these values are used for things like the type of a step, and
;; during evaluation, where they are used as type annotations on THE
;; and NEU.
(struct HO-CLOS ([proc : (-> Value Value)]) #:transparent)


;;; Finding fresh names

;; Find a fresh name, using none of those described in a context.
;;
;; This is the implementation of the Γ ⊢ fresh ↝ x form of
;; judgment. Unlike the rules in the appendix to The Little Typer,
;; this implementation also accepts a name suggestion so that the code
;; produced by elaboration has names that are as similar as possible
;; to those written by the user.
(: fresh (-> Ctx Symbol Symbol))
(define (fresh Γ x)
  (freshen (names-only Γ) x))

;; Find a fresh name, using none of those described in a context nor
;; occurring in an expression. This is used when constructing a fresh
;; binding to avoid capturing a free variable that would otherwise be
;; an error because it points at the context.
(: fresh-binder (-> Ctx Src Symbol Symbol))
(define (fresh-binder Γ expr x)
  (freshen (append (names-only Γ) (occurring-names expr)) x))


;; Find the names that are described in a context, so they can be
;; avoided.
(: names-only (-> Ctx (Listof Symbol)))
(define (names-only Γ)
  (cond
    [(null? Γ) '()]
    [else (cons (car (car Γ)) (names-only (cdr Γ)))]))

;; Find all the names that occur in an expression. For correctness, we
;; need only find the free identifiers, but finding the bound
;; identifiers as well means that the bindings introduced by
;; desugaring expressions are more different from the program as
;; written, which can help readability of internals.
(: occurring-names (-> Src (Listof Symbol)))
(define (occurring-names expr)
  (match (src-stx expr)
    [`(the ,t ,e)
     (append (occurring-names t) (occurring-names e))]
    [`(quote ,x)
     '()]
    [`(add1 ,n)
     (occurring-names n)]
    [`(which-Nat ,tgt ,base ,step)
     (append (occurring-names tgt) (occurring-names base) (occurring-names step))]
    [`(iter-Nat ,tgt ,base ,step)
     (append (occurring-names tgt) (occurring-names base) (occurring-names step))]
    [`(rec-Nat ,tgt ,base ,step)
     (append (occurring-names tgt) (occurring-names base) (occurring-names step))]
    [`(ind-Nat ,tgt ,mot ,base ,step)
     (append (occurring-names tgt) (occurring-names mot) (occurring-names base) (occurring-names step))]
    [(cons '-> (cons t0 ts))
     (append (occurring-names t0) (apply append (map occurring-names ts)))]
    [`(Π ,bindings ,t)
     (append (apply append (map occurring-binder-names bindings)) (occurring-names t))]
    [`(λ ,bindings ,t)
     (append (map binder-var bindings) (occurring-names t))]
    [`(Σ ,bindings ,t)
     (append (apply append (map occurring-binder-names bindings)) (occurring-names t))]
    [`(Pair ,A ,D)
     (append (occurring-names A) (occurring-names D))]
    [`(cons ,A ,D)
     (append (occurring-names A) (occurring-names D))]
    [`(car ,p)
     (occurring-names p)]
    [`(cdr ,p)
     (occurring-names p)]
    [`(:: ,A ,D)
     (append (occurring-names A) (occurring-names D))]
    [`(List ,E)
     (occurring-names E)]
    [`(rec-List ,tgt ,base ,step)
     (append (occurring-names tgt) (occurring-names base) (occurring-names step))]
    [`(ind-List ,tgt ,mot ,base ,step)
     (append (occurring-names tgt) (occurring-names mot) (occurring-names base) (occurring-names step))]
    [`(ind-Absurd ,tgt ,mot)
     (append (occurring-names tgt) (occurring-names mot))]
    [`(= ,A ,from ,to)
     (append (occurring-names A) (occurring-names from) (occurring-names to))]
    [`(same ,e)
     (occurring-names e)]
    [`(replace ,tgt ,mot ,base)
     (append (occurring-names tgt) (occurring-names mot) (occurring-names base))]
    [`(trans ,tgt1 ,tgt2)
     (append (occurring-names tgt1) (occurring-names tgt2))]
    [`(cong ,tgt ,f)
     (append (occurring-names tgt) (occurring-names f))]
    [`(symm ,tgt)
     (occurring-names tgt)]
    [`(ind-= ,tgt ,mot ,base)
     (append (occurring-names tgt) (occurring-names mot) (occurring-names base))]
    [`(Vec ,E ,len)
     (append (occurring-names E) (occurring-names len))]
    [`(vec:: ,hd ,tl)
     (append (occurring-names hd) (occurring-names tl))]
    [`(head ,tgt)
     (occurring-names tgt)]
    [`(tail ,tgt)
     (occurring-names tgt)]
    [`(ind-Vec ,len ,tgt ,mot ,base ,step)
     (append (occurring-names len) (occurring-names tgt)
             (occurring-names mot)
             (occurring-names base) (occurring-names step))]
    [`(Either ,A ,B)
     (append (occurring-names A) (occurring-names B))]
    [`(left ,e)
     (occurring-names e)]
    [`(right ,e)
     (occurring-names e)]
    [`(ind-Either ,tgt ,mot ,l ,r)
     (append (occurring-names tgt) (occurring-names mot) (occurring-names l) (occurring-names r))]
    [(cons (? src? f) (cons arg0 args))
     (append (occurring-names f) (occurring-names arg0) (apply append (map occurring-names args)))]
    [x
     (if (and (symbol? x) (var-name? x))
       (list x)
       '())]))

(: occurring-binder-names (-> Typed-Binder (Listof Symbol)))
(define (occurring-binder-names b)
  (match b
    [(list (binder where x) t)
     (cons x (occurring-names t))]))


;; Local Variables:
;; eval: (put 'Π 'racket-indent-function 1)
;; eval: (put 'Σ 'racket-indent-function 1)
;; eval: (put 'go-on 'racket-indent-function 1)
;; eval: (setq whitespace-line-column 70)
;; End:


