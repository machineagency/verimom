#lang rosette

(provide (all-defined-out))


; Lifts Racket dictionaries to work in Rosette (assuming the keys are always
; concrete, which is true in our case).
(require rosette/lib/lift)
(define-lift env-ref [(dict? symbol?) dict-ref])
(define-lift env-set [(dict? symbol? integer?) dict-set])

; Returns the result of evaluating the given Verimom program
; or #f if the program aborts.
(define (interpret prog)
  (match-define `(verimom ,_ (,args ...) : (,rets ...) ,_ ... ,S) prog)
  (define env (interpretS S (list)))
  (and env (for/list ([ret rets]) (env-ref env ret))))

; Interprets a statement. Returns an updated environment
(define (interpretS S env)
  (and env
   (match S
     [`(machine ,name ,acceptsS ,envelopeS))
        (???(interpretS acceptsS) (interpretS envelopeS))]
     [`(accepts ,axes ...)
        ???]
     [`(envelope ,dims ...)
        ???]
     [`(path-closed ,name ...)
        (env-set env name 42)]))) ;TODO: actually set according to pts

; Interprets an expression, including point expressions. Returns the result
; of the evaluation.
(define (interpretE E env)
  (match E
    [(? integer?) E]
    [(? symbol?)  (env-ref env E)]
    [`(pt ,x ,y) (list (interpretE x) (interpretE y))]
    [`(- ,E1 ..1) (apply - (map (curryr interpretE env) E1))]
    [`(+ ,E1 ...) (apply + (map (curryr interpretE env) E1))]
    [`(* ,E1 ...) (apply * (map (curryr interpretE env) E1))]))

; Define an object to represent Verimom programs. Each object contains
; an AST as a nested list of symbols for the program, as well as a
; a Racket procedure that calls the Verimom interpreter on the AST.
(struct verimom-obj (ast proc)
  #:transparent
  #:property prop:procedure
  [struct-field-index proc])

; Binds the identifier id to a program object that represents 
; the given Verimom program.
(define-syntax (verimom stx)
  (syntax-case stx (:)
    [(_ id contract ... stmt)
     (syntax/loc stx 
       (define id 
         (let* ([ast `(verimom id contract ... stmt)]
                [id (lambda () (interpret ast))])
           (verimom-obj ast id))))]))


