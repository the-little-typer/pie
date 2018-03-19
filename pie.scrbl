#lang scribble/manual

@(require (for-label (only-meta-in 0 pie))
          racket/sandbox scribble/example
          (for-syntax racket/base syntax/parse))

@(define ev
   (parameterize ([sandbox-output 'string]
                  [sandbox-error-output 'string])
     (make-evaluator 'pie)))

@(define-syntax (ex stx)
   (syntax-parse stx
     [(_ e ...)
      (syntax/loc stx
        (examples #:eval ev e ...))]))

@(define-syntax (pie stx)
   (syntax-parse stx
     [(_ e ...)
      (syntax/loc stx
        (racket e ...))]))

@(define-syntax (pieblock stx)
   (syntax-parse stx
     [(_ e ...)
      (syntax/loc stx
        (racketblock e ...))]))

@(define-syntax (def-type-constructor stx)
   (syntax-parse stx
     [(_ con:id content ...)
      (syntax/loc stx
        (defform #:kind "type constructor" #:id con con content ...))]
     [(_ con-expr content ...)
      (syntax/loc stx
        (defform #:kind "type constructor" con-expr content ...))]))


@(define-syntax (def-constructor stx)
   (syntax-parse stx
     [(_ con:id content ...)
      (syntax/loc stx
        (defthing #:kind "constructor" con content ...))]
     [(_ con-expr content ...)
      (syntax/loc stx
        (defproc #:kind "constructor" con-expr content ...))]))


@(define-syntax (def-eliminator stx)
   (syntax-parse stx
     [(_ elim-expr content ...)
      (syntax/loc stx
        (defproc #:kind "eliminator" elim-expr content ...))]))


@title{The Pie Reference}
@author{David Thrane Christiansen and Daniel P. Friedman}



@defmodule[pie #:lang]{
 Pie is a little language with dependent types that accompanies
 @hyperlink["http://thelittletyper.com"]{@emph{The Little Typer}}.
}

@table-of-contents[]

@section{Using Pie in DrRacket}
Pie is implemented as a Racket language. While other editors may work, Pie
is currently supported best in DrRacket.

After installing Pie from the Racket package database, open DrRacket.
Change the first line to read @tt{#lang pie}, and then start typing.
If DrRacket's "Background Expansion" feature is enabled, the type checker
will run every time the file is modified, whether or not it is run.
Otherwise, invoke the type checker using the "Run" button. It may be
convenient to enable the option in DrRacket to show gold highlighting on
errors, because it causes type errors to be highlighted while typing.

Alternatively, it is also possible to use any editor to create a Pie program,
and then save it to a file. Run the file with the command-line version of
Racket to test it.

The 
@other-doc['(lib "todo-list/scribblings/todo-list.scrbl")]
is supported by Pie. Each @pie[TODO] in the program is listed.

@section{General-Purpose Expressions}
@defform[#:kind "type annotation" (the type expr)]{
 Asserts that @pie[expr] is a @pie[type]. This can be necessary when there is
 insufficient information for Pie to discover an expression's type.
 @ex[(eval:error nil)
     (the (List Nat)
       nil)
     (eval:error (cons 2 (same 2)))
     (the (Σ ((n Nat))
            (= Nat n n))
       (cons 2 (same 2)))
     (the (Σ ((n Nat))
            (= Nat n 2))
       (cons 2 (same 2)))]
}
@defform[#:kind "incomplete expression" #:id TODO TODO]{
 @pie[TODO] represents a part of a program that is not yet written, corresponding
 to the empty boxes in @emph{The Little Typer}. Users may optionally leave a note
 or other expression behind as a reminder.
}

@section{Types, Constructors, and Eliminators}
@subsection{Absurd}
@def-type-constructor[Absurd]{
 @pie[Absurd] is a type with no values.
}
@def-eliminator[(ind-Absurd [target Absurd] [motive U]) motive]{
 Given an @pie[Absurd] expression, @pie[ind-Absurd] can have any type at all.
@ex[(the (→ Absurd
           Nat)
      (λ (nope)
        (ind-Absurd nope Nat)))]
}

@subsection{Trivial}
@def-type-constructor[Trivial]{@pie[Trivial] is a type with exactly one value.}
@def-constructor[sole Trivial]{
 @pie[sole] is the only @pie[Trivial] value, and every @pie[Trivial] expression
 is the same @pie[Trivial] as @pie[sole].
 @ex[sole
     (check-same (→ Trivial
                   Trivial)
       (λ (x)
         sole)
       (λ (y)
         y))]
}

@subsection{Atoms}
@def-type-constructor[Atom]{Atoms are like Lisp symbols.}
@def-constructor[(quote [atom identifier]) Atom]{
 Each atom is a constructor. @pie[quote] is always written with a single
 tick mark.
 @ex['grønkål
     'agurk]
}

@subsection{Natural Numbers}
@def-type-constructor[Nat]{
 The natural numbers, called @pie[Nat], are all the numbers greater than or equal to zero.
}
@def-constructor[zero Atom]{@pie[zero] is the smallest @pie[Nat].}
@def-constructor[(add1 [n Nat]) Atom]{@pie[add1] makes a @pie[Nat] one larger.}
@def-eliminator[(which-Nat [target Nat] [base _X] [step (-> Nat _X)]) _X]{
 @pie[which-Nat] is a case operator on @pie[Nat].
 @ex[(which-Nat 0 0 (λ (smaller) smaller))
     (which-Nat 17 0 (λ (smaller) smaller))]
}
@def-eliminator[(iter-Nat [target Nat] [base _X] [step (-> Nat _X)]) _X]{
 @pie[iter-Nat] applies @pie[step] to @pie[base] @pie[target] times.
 @ex[(iter-Nat 5
       0
       (λ (x)
         (add1 (add1 x))))]
}
@def-eliminator[(rec-Nat [target Nat] [base _X] [step (-> Nat _X _X)]) X]{
 @pie[rec-Nat] is primitive recursion on @pie[Nat]. If @pie[target] is
 @pie[zero], then the whole expression is @pie[base]. If @pie[target] is
 @pie[(add1 _n)], then the whole expression is
 @pie[(step _n (rec-Nat _n base step))].
}
@def-eliminator[(ind-Nat [target Nat]
                   [motive (-> Nat U)]
                   [base (motive zero)]
                   [step (Π ((n Nat))
                           (-> (motive n)
                             (motive (add1 n))))])
                 (motive target)]{
 @pie[ind-Nat] is induction on @pie[Nat]. @pie[motive] is an @pie[(→ Nat U)],
 and the whole expression's type is @pie[(motive target)]. @pie[ind-Nat]
 computes identically to @pie[rec-Nat]; the type is, however, more expressive.
}

@subsection{Pairs}
@def-type-constructor[(Σ ((x A1) (y A2) ...) D)]{
 The values of @pie[(Σ ((_x _A)) _D)] are @pie[(cons _a _d)], where
 @pie[_a] is an @pie[_A] and the type of @pie[_d] is found by consistently
 replacing @pie[_x] with @pie[_a] in @pie[_D].

 @pie[(Σ ((x A1) (y A2) ...) D)] is an abbreviation for the nested @pie[Σ]-expressions
 @pieblock[(Σ ((x A1))
             (Σ ((y A2))
               ...
               D))]
}
@def-type-constructor[(Sigma ((x A1) (y A2) ...) D)]{@pie[Sigma] is an alias for @pie[Σ]}
@def-type-constructor[(Pair A D)]{A shorter way of writing @pie[(Σ ((x A)) D)] when @pie[x] is not used.}
@def-constructor[(cons [a A] [d D^]) (Σ ((x A)) D)]{
 @pie[cons] is the constructor for @pie[Σ]. @pie[D^] is the result of
  consistently replacing each @pie[x] in @pie[D] with @pie[a].
}
@def-eliminator[(car [p (Σ ((x _A)) _D)]) _A]{
 The first projection of a pair. If @pie[p] is a @pie[(Σ ((_x _A)) _D)], then
 @pie[(car p)] is an @pie[_A]. Furthermore, @pie[(car (cons _a _d))] is @pie[_a].
}
@def-eliminator[(cdr [p (Σ ((x _A)) _D)]) _D]{
The second projection of a pair. If @pie[p] is a @pie[(Σ ((_x _A)) _D)], then
 @pie[(cdr p)] is a @pie[_D] where each @pie[_x] has been replaced by @pie[(car p)].
 Furthermore, @pie[(cdr (cons _a _d))] is @pie[_d].
}

@subsection{Functions}
@def-type-constructor[(Π ((x X1) (y X2) ...) B)]{
 Function types are written with @pie[Π].
 All functions take exactly one argument, and what appears to be a multiple-argument
 function or function type is actually a Curried function. In other words,
 @pie[(Π ((x X1) (y X2) ...) B)] is an abbreviation for
 @pieblock[(Π ((x X1))
             (Π ((y X2))
               ...
               B))]
 The type of a function application is found by substituting the actual argument for
 the argument name in the return type.
 @ex[((the (Π ((n Nat))
             (= Nat n n))
        (λ (n)
          (same n)))
      5)
     ((the (Π ((n Nat))
             (= Nat n n))
        (λ (n)
          (same n)))
      15)]
}
@def-type-constructor[(Pi ((x X1) (y X2) ...) B)]{
 @pie[Pi] is an alias for @pie[Π].
}
@def-type-constructor[(→ X1 X2 ... B)]{
 @pie[→], pronounced "arrow", is shorter way of writing @pie[(Π ((x X1) (x X2) ...) B)] when the identifiers @racket[x ...] are not used.}
@def-type-constructor[(-> X1 X2 ... B)]{@pie[->] is an alias for @pie[→].}
@defform[#:kind "constructor"
         #:literals (x1 x2)
          (λ (x1 x2 ...) b)]{
 Functions are constructed with @pie[λ]. @pie[(λ (x1 x2 ...) b)] is a
 @pie[(Π ((x1 X1) (x2 X2) ...) B)] if when @pie[x1] is a @pie[X1], @pie[x2] is a @pie[X2], ...,
 then @pie[b] is a @pie[B].

 What may appear to be multiple-argument functions are actually nested one-argument functions.
 @ex[(the (→ Atom Atom
            Atom)
        (λ (food beverage)
          food))
     (the (→ Atom
            (→ Atom
              Atom))
        (λ (food)
          (λ (beverage)
            food)))
     (check-same (→ Atom Atom
                   Atom)
       (λ (food)
         (λ (beverage)
           beverage))
       (λ (food beverage)
         beverage))]
}
@defform[#:kind "constructor" (lambda (x1 x2 ...) b)]{@pie[lambda] is an alias for @pie[λ].}

@subsection{Lists}
@def-type-constructor[(List E)]{
  @pie[(List E)] is the type of lists in which all entries are @pie[E]s.
}
@def-constructor[nil (List _E)]{
 @ex[(the (List Atom) nil)
     (eval:error nil)
     (the (List (→ Nat
                  Nat))
       nil)]
}
@def-constructor[(:: [e _E] [es (List _E)]) (List _E)]{
  @ex[(:: 0 (:: 1 (:: 2 nil)))
      (eval:error (:: 0 (:: 'one (:: 2 nil))))]
}
@def-eliminator[(rec-List [target (List _E)]

                           [base _X]
                           [step (-> E (List _E) _X _X)])
                 _X]{
 @pie[rec-List] is primitive recursion on lists.
 If @pie[target] is @pie[nil], the result is @pie[base]. If @pie[target]
 is @pie[(:: _e _es)], then the result is @pie[(step _e _es (rec-List _es base step))].
 @ex[(rec-List (the (List Atom) nil)
       zero
       (λ (e es len-1)
         (add1 len-1)))
     (rec-List (:: 'rødbeder
                 (:: 'gulerødder
                   (:: 'kartofler nil)))
       zero
       (λ (e es len-1)
         (add1 len-1)))]
}
@def-eliminator[(ind-List [target (List _E)]
                           [motive (-> (List _E) U)]
                           [base (motive nil)]
                           [step (Π ((e _E)
                                     (es (List _E)))
                                   (-> (motive es)
                                     (motive (:: e es))))])
                 (motive target)]{
 @pie[ind-List] is induction on lists. When @pie[target] is a @pie[(List _E)], t
 the whole expression's type is @pie[(motive target)], the type of
 @pie[base] is @pie[(motive nil)], and the type of @pie[step] is
 @pieblock[(Π ((e _E)
               (es (List _E)))
             (→ (motive es)
               (motive (:: e es))))].
 @pie[ind-List] computes just like @pie[rec-List].
 
 @ex[(ind-List (:: 'ananas
                 (:: 'granatæble
                   nil))
       (λ (es)
         Nat)
       zero
       (λ (e es len)
         (add1 len)))
     (ind-List (:: 'ananas
                 (:: 'granatæble
                   nil))
       (λ (es)
         (= (List Atom) es es))
       (same nil)
       (λ (e es es=es)
         (cong es=es
           (the (→ (List Atom)
                  (List Atom))
             (λ (xs)
               (:: e xs))))))]
}

@subsection{Vectors}
@def-type-constructor[(Vec E len)]{
  A @pie[(Vec E len)] is a list that contains precisely @pie[len] entries,
 each of which is an @pie[E].
}
@def-constructor[vecnil (Vec _E zero)]{
 @pie[vecnil] is an empty @pie[Vec].
 @ex[(the (Vec Nat zero) vecnil)
     (the (Vec Atom zero) vecnil)
     (eval:error (the (Vec Atom 4) vecnil))
     (eval:error vecnil)]
}
@def-constructor[(vec:: [e _E] [es (Vec _E k)]) (Vec _E (add1 k))]{
  @ex[(the (Vec Nat 2) (vec:: 17 (vec:: 6 vecnil)))
      (eval:error (the (Vec Nat 3) (vec:: 17 (vec:: 6 vecnil))))
      (eval:error (vec:: 17 (vec:: 6 vecnil)))]
}
@def-eliminator[(head [es (Vec _E (add1 k))]) _E]{
 @pie[head] finds the first entry in a non-empty @pie[Vec].
  @ex[(head (the (Vec Atom 1) (vec:: 'æbler vecnil)))
      (eval:error (head (the (Vec Atom 0) vecnil)))]
}
@def-eliminator[(tail [es (Vec _E (add1 k))]) (Vec _E k)]{
 @pie[tail] finds the all but the first entry in a non-empty @pie[Vec].
 @ex[(tail (the (Vec Atom 2) (vec:: 'pærer (vec:: 'æbler vecnil))))
     (eval:error (tail (the (Vec Atom 0) vecnil)))]
}
@def-eliminator[(ind-Vec [target-1 Nat]
                          [target-2 (Vec _E target-1)]
                          [motive (Π ((k Nat))
                                    (→ (Vec _E k)
                                      U))]
                          [base (motive zero vecnil)]
                          [step (Π ((k Nat)
                                    (e _E)
                                    (es (Vec _E k)))
                                  (→ (motive k es)
                                    (motive (add1 k) (vec:: e es))))])
                 (motive target-1 target-2)]{
 Induction on vectors is used to prove things about any vector.
 @pie[target-1] is the length, and @pie[target-2] is the vector itself.
 The motive is a
 @pieblock[(Π ((k Nat))
             (→ (Vec _E k)
               U))]
 The @pie[base] is a @pie[(motive zero vecnil)],
 and the @pie[step] is a
 @pieblock[(Π ((k Nat)
               (e _E)
               (es (Vec _E k)))
             (→ (motive k es)
               (motive (add1 k) (vec:: e es))))]
}

@subsection{Either}
@def-type-constructor[(Either L R)]{
 @pie[Either] represents that there are two possibilities: either an @pie[L]
 with @pie[left] on top, or an @pie[R] with @pie[right] on top.
}
@def-constructor[(left [l (Either _L _R)]) _L]{
 @ex[(the (Either Nat Atom) (left 3))
     (eval:error (the (Either Nat Atom) (left 'rosenkål)))]
}
@def-constructor[(right [r (Either _L _R)]) _R]{
 @ex[(the (Either Nat Atom) (right 'blomkål))
     (eval:error (the (Either Nat Atom) (right 8)))]
}
@def-eliminator[(ind-Either [target (Either _X _Y)]
                             [motive (→ (Either _X _Y) U)]
                             [on-left (Π ((l _L))
                                        (motive (left l)))]
                             [on-right (Π ((r _R))
                                         (motive (right r)))])
                 (motive target)]{
  Induction on @pie[Either] consists of showing how to fulfill the motive for
 both constructors.
 @ex[(ind-Either (the (Either Nat Atom) (left 5))
        (λ (e)
          Nat)
        (λ (n)
          n)
        (λ (a)
          17))
     (ind-Either (the (Either Nat Atom) (right 'peberfrugt))
        (λ (e)
          Nat)
        (λ (n)
          n)
        (λ (a)
          17))]
}

@subsection{Equality}
@def-type-constructor[(= X from to)]{
  The equality type's values are evidence that @pie[from] and @pie[to]
 are equal.
}
@def-constructor[(same [e _X]) (= _X e e)]{
  If @pie[e] is an @pie[X], then @pie[(same e)] is an @pie[(= X e e)], because
  @pie[e] is the same @pie[X] as @pie[e].
  @ex[(the (= Nat 2 2) (same 2))]
}
@def-eliminator[(replace [target (= _X _from _to)]
                          [motive (→ _X U)]
                          [base (motive _from)])
                 (motive _to)]{
 If @pie[target] is an @pie[(= _X _from _to)], @pie[motive] is an
 @pieblock[(→ _X
             U)]
 and @pie[base] is a @pie[(motive _from)], then
 @pie[(replace target motive base)] is a @pie[(motive _to)].
}
@def-eliminator[(symm [target (= _A _from _to)]) (= _A _to _from)]{
 If @pie[target] is an @pie[(= _A _from _to)], then @pie[(symm target)] is an
 @pie[(= _A _to _from)].
 @ex[(the (Π ((x Nat)
              (y Nat))
            (→ (= Nat x y)
              (= Nat y x)))
       (λ (x y p)
         (symm p)))]
}
@def-eliminator[(trans [target-1 (= _X _from _middle)]
                        [target-2 (= _X _middle _to)])
                 (= _X _from _to)]{
  @pie[trans] is used to "glue together" evidence of equality. If @pie[target-1]
 is an @pie[(= _X _from _middle)] and @pie[target-2] is an @pie[(= _X _middle _to)],
 then @pie[(trans target-1 target-2)] is an @pie[(= _X _from _to)].
}
@def-eliminator[(cong [target (= _X _from _to)] [fun (→ _X _Y)])
                 (= _Y (fun _from) (fun _to))]{
 @pie[cong] shows that all functions respect equality. In particular,
 if @pie[target] is an @pie[(= _X _from _to)] and @pie[fun] is an
 @pieblock[(→ _X
             _Y)]
 then @pie[(cong target fun)] is an
 @pieblock[(= _X (fun _from) (fun _to))]
}
@def-eliminator[(ind-= [target (= _A _from _to)]
                        [motive (Π ((x _A))
                                  (-> (= _A _from x)
                                    U))]
                        [base (motive _from (same _from))])
                 (motive _to target)]{
  The induction principle on equality evidence takes a target which is an
  @pie[(= _A _from _to)], a motive which is a
  @pieblock[(Π ((x _A))
              (-> (= _A _from x)
                U))]
  and a base which is a @pie[(motive _from (same _from))]. The entire expression
  is then a @pie[(motive _to target)].
}

@subsection{Universe}
@def-type-constructor[U]{
 The universe describes all types except itself and those types that could contain
 @pie[U].
 @ex[(the U Nat)
     (eval:error (the U U))
     (the U (List Atom))
     (eval:error (the U (List U)))]
}

@section{Declarations}
In addition to expressions, Pie has three syntactic forms that are only valid
at the top level of a program.

@subsection{Definitions}
@defform[#:kind "declaration" (claim x type)]{
 Before using @pie[define] to associate a name with an expression, it is first necessary to associate
 the expression's type with the name using @pie[claim].
}
@defform[#:kind "declaration" (define x expr)]{
 Associate the expression @pie[expr] with the name @pie[x], after having already @pie[claim]ed its type.
}

@subsection{Testing Pie programs}
@defform[#:kind "declaration" (check-same type expr1 expr2)]{
 Check that @pie[expr1] is the same @pie[type] as @pie[expr2], and fail if not.

 @ex[(check-same Nat 4 4)
     (check-same Atom 'kirsebær 'kirsebær)
     (eval:error (check-same Atom 4 'four))
     (eval:error (check-same Atom 'kirsebær 'hindbær))]

            
 Because of the η-rules for @pie[Π] and @pie[Absurd], every proof of a negation
 is the same as every other proof. This is useful when testing programs that
 produce proofs.

 @ex[(check-same (→ (→ (= Nat 2 3)
                      Absurd)
                    (→ (= Nat 2 3)
                      Absurd)
                   (→ (= Nat 2 3)
                     Absurd))
       (λ (f g)
         f)
       (λ (f g)
         g))]
}
