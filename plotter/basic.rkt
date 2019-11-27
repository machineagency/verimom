#lang rosette

(require "verimom.rkt")
(provide (all-defined-out))

; Define a path in verimom - TODO: reconsider and/or remove args
(verimom
    (machine 'm (accepts x y) (envelope 100 100))
    (path-closed 'original (pt 0 0) (pt 20 0) (pt 20 20) (pt 0 20))
    (scale 'original 2))

