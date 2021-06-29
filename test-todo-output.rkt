#lang racket/base

(require rackunit racket/port)

(check-equal?
 (with-output-to-string
   (lambda () (dynamic-require "todo-test.pie" #f)))
 "<pkgs>/pie/todo-test.pie:10:15: TODO:\n           n : Nat\n         n-1 : Nat\n peas-of-n-1 : (Vec Atom n-1)\n------------------------------\n Atom\n\n\n<pkgs>/pie/todo-test.pie:10:20: TODO:\n           n : Nat\n         n-1 : Nat\n peas-of-n-1 : (Vec Atom n-1)\n------------------------------\n (Vec Atom n-1)\n\n\n<pkgs>/pie/todo-test.pie:13:17: TODO: Nat\n\n<pkgs>/pie/todo-test.pie:15:19: TODO: \n (Π ((n Nat))\n  (Vec Atom n))\n\n\n")
