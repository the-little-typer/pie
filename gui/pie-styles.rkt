#lang racket/base
(require racket/gui)
(require framework)

(provide (all-defined-out))

(define current-pie-gui-font-size
  (make-parameter 40))

(define (exact n)
  (inexact->exact (round n)))

(define pie-styles<%>
  (interface (editor<%>)
    [text-style (->m (is-a?/c style<%>))]
    [keyword-style (->m (is-a?/c style<%>))]
    [parenthesis-style (->m (is-a?/c style<%>))]
    [data-constructor-style (->m (is-a?/c style<%>))]
    [type-constructor-style (->m (is-a?/c style<%>))]
    [definition-name-style (->m (is-a?/c style<%>))]
    [definition-name-delta (->m (is-a?/c style-delta%))]
    [var-style (->m (is-a?/c style<%>))]
    [change-font-size (->m exact-integer? void?)]))

(define pie-styles-mixin
  (mixin (color:text<%>) (pie-styles<%>)
    (super-new)
    (define sans-face "CMU Bright")
    (define serif-face "Latin Modern Roman")

    (define style-list (send this get-style-list))
    (define basic (send style-list basic-style))
    (define basic-delta
      (make-object style-delta%
                   'change-size (exact (current-pie-gui-font-size))))
    (send basic-delta set-face sans-face)
    (send basic-delta set-size-in-pixels-on #t)
    (define new-basic (send style-list find-or-create-style basic basic-delta))
    (send style-list replace-named-style "Basic" new-basic)
    (send style-list replace-named-style "Standard" new-basic)

    (define var-delta (make-object style-delta%))
    (send var-delta set-face sans-face)
    (send var-delta set-style-on 'italic)
    (send var-delta set-size-in-pixels-on #t)
    (define the-var-style
      (send style-list find-or-create-style new-basic var-delta))

    (define/public (var-style) the-var-style)

    (define text-delta
      (make-object style-delta%))
    (send text-delta set-face serif-face)
    (send text-delta set-size-in-pixels-on #t)
    (define book-style
      (send style-list find-or-create-style new-basic
            text-delta))
    (send style-list new-named-style "book-text" book-style)
    (define/public (text-style) book-style)

    (define parenthesis-delta
      (make-object style-delta%))
    (send parenthesis-delta set-face sans-face)
    (send parenthesis-delta set-weight-on 'bold)
    (send parenthesis-delta set-delta-foreground "DimGray")
    (send parenthesis-delta set-size-in-pixels-on #t)
    (define paren-style
      (send style-list find-or-create-style new-basic
            parenthesis-delta))
    (send style-list new-named-style "parenthesis" paren-style)

    (define/public (parenthesis-style) paren-style)

    (define type-ctor-delta
      (make-object style-delta%))
    (send type-ctor-delta set-face sans-face)
    (send type-ctor-delta set-size-in-pixels-on #t)
    (define type-ctor-style
      (send style-list find-or-create-style new-basic
            type-ctor-delta))
    (send style-list new-named-style "type-ctor" type-ctor-style)

    (define/public (type-constructor-style) type-ctor-style)

    (define definition-delta
      (make-object style-delta%))
    (define/public (definition-name-delta) definition-delta)
    (send definition-delta set-face sans-face)
    (send definition-delta set-weight-on 'bold)
    (send definition-delta set-style-on 'italic)
    (send definition-delta set-size-in-pixels-on #t)
    (define definition-style
      (send style-list find-or-create-style new-basic
            definition-delta))
    (send style-list new-named-style "definition" definition-style)

    (define/public (definition-name-style) definition-style)

    (define data-ctor-delta
      (make-object style-delta%))
    (send data-ctor-delta set-face sans-face)
    (send data-ctor-delta set-size-in-pixels-on #t)
    (define data-ctor-style
      (send style-list find-or-create-style new-basic
            data-ctor-delta))
    (send style-list new-named-style "data-ctor" data-ctor-style)
    (send style-list new-named-style "constant" data-ctor-style)
    (define/public (data-constructor-style) data-ctor-style)

    (define keyword-delta
      (make-object style-delta%))
    (send keyword-delta set-face sans-face)
    (send keyword-delta set-weight-on 'bold)
    (send keyword-delta set-size-in-pixels-on #t)
    (define pie-keyword-style
      (send style-list find-or-create-style new-basic
            keyword-delta))
    (send style-list new-named-style "keyword" pie-keyword-style)
    (define/public (keyword-style) pie-keyword-style)

    (define/public (change-font-size amount)
      (define style-list (send this get-style-list))
      (define basic (send style-list basic-style))
      (define δ
        (cond
          [(> amount 0)
           (make-object style-delta% 'change-bigger amount)]
          [(< amount 0)
           (make-object style-delta% 'change-smaller (- amount))]
          [else
           (make-object style-delta%)]))
      (send basic set-delta δ)
      (void))))
