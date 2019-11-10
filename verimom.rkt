#lang rosette

(provide (all-defined-out))


; Lifts Racket dictionaries to work in Rosette (assuming the keys are always
; concrete, which is true in our case).
(require rosette/lib/lift)
(define-lift env-ref [(dict? symbol?) dict-ref])
(define-lift env-set [(dict? symbol? integer?) dict-set])

; TODO: interpreter

