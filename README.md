# Pie: A Little Language with Dependent Types

This is Pie, the companion language for _The Little Typer_ by Daniel P. Friedman and David Thrane Christiansen.

## How to Use Pie

Pie is a [Racket](http://racket-lang.org) language, requiring Racket version 6.11 or newer. After installation, Racket will interpret any file beginning with `#lang pie` as a Pie program.

### TODO items

If you can't figure out what to write at some point in a Pie program, it's OK to leave behind a space to be filled out later. This corresponds to the empty boxes in _The Little Typer_. These TODOs are written `TODO` in Pie.

### DrRacket Integration

Pie provides additional information to DrRacket, including tooltips and other metadata. Point the mouse at a pair of parentheses, a name, or a Pie constructor or type constructor to see information about the expression.

Additionally, Pie supports the [DrRacket TODO list](https://github.com/david-christiansen/todo-lilst) for incomplete programs.

### Command-Line REPL

If you prefer an editor other than DrRacket, it may be convenient to start a Pie REPL on a command line. To do so, use the command `racket -l pie -i` to start Racket with the `pie` language in interactive mode.


## Installation Instructions
Pie is not yet officially released. However, it is on the Racket package server.

### From DrRacket

Click the "File" menu, and then select "Install Package...". Type `pie` in the box, and click the "Install" button.

### From a Command Line

Run the following command:
`raco pkg install pie`

## Updates

Because it exists to support a book, the Pie language is finished and will not change. However, this _implementation_ of Pie might someday acquire additional features, or it might require updates to keep up with new computers. In that case, update it as you would any Racket package.

### Updating in DrRacket

Click the "File" menu, and then select "Install Package...". Type `pie` in the box, and click the "Update" button.

### Updating from a Command Line

The command `raco pkg update pie` updates Pie.
