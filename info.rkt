#lang info
(define collection "pie")
(define version "0.01")
(define deps '(("base" #:version "6.5")
               "data-lib" "gui-lib" "slideshow-lib" "pict-lib"
               "typed-racket-lib" "typed-racket-more"
               "parser-tools-lib" "syntax-color-lib"
               "rackunit-lib"))
(define pkg-desc "A little dependently typed language to be used with The Little Typer")

(define build-deps '("todo-list" "scribble-lib" "racket-doc" "sandbox-lib"
                                 "rackunit-lib"))
(define scribblings '(("pie.scrbl" () (language) "pie")))
