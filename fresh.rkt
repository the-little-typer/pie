#lang typed/racket/base

(require racket/string)
(provide freshen)

(: freshen (-> (Listof Symbol) Symbol Symbol))
(define (freshen used x)
  (if (memv x used)
      (let ([split (split-name x)])
        (freshen-aux used split))
      x))

(: freshen-aux (-> (Listof Symbol) (Pair String Number) Symbol))
(define (freshen-aux used split)
  (let ([joined (unsplit-name split)])
    (if (memv joined used)
        (freshen-aux used (next-split-name split))
        joined)))

(: next-split-name (-> (Pair String Number) (Pair String Number)))
(define (next-split-name split)
  (cons (car split) (add1 (cdr split))))

(: unsplit-name (-> (Pair String Number) Symbol))
(define (unsplit-name split)
  (string->symbol
   (string-append (car split) (number->subscript-string (cdr split)))))

(: string-replace* (-> String (Listof (Pair String String)) String))
(define (string-replace* str replacements)
  (cond
    [(null? replacements) str]
    [else
     (let ([from (car (car replacements))]
           [to (cdr (car replacements))])
       (string-replace* (string-replace str from to)
                        (cdr replacements)))]))

(: subscript-replacements (Listof (Pair String String)))
(define subscript-replacements
  '(("0" . "₀")
    ("1" . "₁")
    ("2" . "₂")
    ("3" . "₃")
    ("4" . "₄")
    ("5" . "₅")
    ("6" . "₆")
    ("7" . "₇")
    ("8" . "₈")
    ("9" . "₉")))

(: non-subscripts (Listof (Pair String String)))
(define non-subscripts
  '(("₀" . "0")
    ("₁" . "1")
    ("₂" . "2")
    ("₃" . "3")
    ("₄" . "4")
    ("₅" . "5")
    ("₆" . "6")
    ("₇" . "7")
    ("₈" . "8")
    ("₉" . "9")))


(: subscript-digit? (-> Char Boolean))
(define (subscript-digit? c)
  (if (assoc (string c) non-subscripts)
      #t
      #f))

(: subscript->number (-> String Number))
(define (subscript->number str)
  (safe-string->number (string-replace* str non-subscripts)))

(: number->subscript-string (-> Number String))
(define (number->subscript-string n)
  (string-replace* (number->string n) subscript-replacements))

(: split-name (-> Symbol (Pair String Number)))
(define (split-name name)
  (let ([str (symbol->string name)])
    (split-name-aux str (sub1 (string-length str)))))

(: split-name-aux (-> String Integer (Pair String Number)))
(define (split-name-aux str i)
  (cond
    [(zero? i)
     (cond
       [(subscript-digit? (string-ref str i))
        (cons "x" (subscript->number str))]
       [else (cons (string (string-ref str i))
                   (subscript->number (substring str i (string-length str))))])]
    [(subscript-digit? (string-ref str i))
     (split-name-aux str (sub1 i))]
    [else (cons
           (substring str 0 (add1 i))
           (subscript->number (substring str i (string-length str))))]))

(: safe-string->number (-> String Number))
(define (safe-string->number str)
  (let ([num (string->number str)])
    (if (eqv? num #f)
        1
        num)))

(module+ test
  (require typed/rackunit)
  (check-eqv? (freshen '(x) 'x)
              'x₁)
  (check-eqv? (freshen '(x x₁ x₂) 'x)
              'x₃)
  (check-eqv? (freshen '(x x1 x2) 'y)
              'y)
  (check-eqv? (freshen '(r2d r2d₀ r2d₁) 'r2d)
              'r2d₂)
  (check-eqv? (freshen '() 'A)
              'A)
  (check-eqv? (freshen '(x₁) 'x₁) 'x₂)
  (check-eqv? (freshen '() 'x₁) 'x₁)
  (check-eqv? (freshen '() (string->symbol "₉₉"))
              (string->symbol "₉₉"))
  (check-eqv? (freshen (list (string->symbol "₉₉")) (string->symbol "₉₉"))
              'x₉₉)
  (check-eqv? (freshen (list (string->symbol "₉₉") 'x₉₉) (string->symbol "₉₉"))
              'x₁₀₀))
