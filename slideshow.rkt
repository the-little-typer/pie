#lang racket

(require "basics.rkt" "gui/main.rkt" "gui/pie-styles.rkt" "gui/print-gui.rkt")
(require (only-in slideshow slide interactive inset text))
(require (only-in racket/gui/base get-display-size))
(require (only-in racket/gui
                  editor-canvas%
                  add-editor-keymap-functions
                  add-text-keymap-functions))
(require (only-in framework panel:vertical-dragable%))

(provide pie-slide)

(define (pie-on-slide-frame f
                            #:initial-contents [contents ""]
                            #:font-size [font-size #f]
                            #:pie-context [pie-context init-ctx])
  (define panel (new panel:vertical-dragable% [parent f]))
  (send panel set-orientation (pie-slide-orientation-horizontal?))
  (parameterize ([current-pie-gui-font-size (or font-size 40)])
    (define fb (new pie-feedback%))
    (define ed (new pie-text%
                    [feedback fb]
                    [pie-context pie-context]
                    [initial-contents contents]))

    (define c (new editor-canvas% [parent panel] [editor ed] [style '(hide-hscroll auto-vscroll no-border)]))
    (define fbc (new editor-canvas% [parent panel] [editor fb] [style '(hide-hscroll auto-vscroll no-border)]))

    (send panel set-percentages '(2/3 1/3))

    (for ([ed (list fb ed)])
      (define keymap (send ed get-keymap))
      (add-editor-keymap-functions keymap)
      (add-text-keymap-functions keymap)))

  void)

(define (pie-slide contents
                   #:title [title ""]
                   #:font-size [font-size #f]
                   #:pie-context [pie-context init-ctx])
  (slide #:title title
         (interactive (inset (text "Pie") 450 300)
                      (lambda (f)
                        (pie-on-slide-frame
                         f
                         #:initial-contents contents
                         #:font-size (and font-size
                                          (let-values ([(h w)
                                                        (get-display-size #t)])
                                            (round (* (/ h 768) font-size))))
                         #:pie-context pie-context)))))
