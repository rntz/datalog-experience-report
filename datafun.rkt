#lang racket

;; An implementation of mini-Datafun (WITHOUT types, monotonicity, termination
;; checking, or semilattice types other than finite sets, but WITH fixed points
;; and set comprehensions) in miniKanren.
;;
;; TODO:
;; - booleans & conditionals?
;; - {,in}equality tests?
;; - MORE EXAMPLES!

(require "fast-mk/mk.rkt" "macros.rkt" "lists.rkt" "sets.rkt")

(provide (all-defined-out))

;; could I write a *type-directed* eval?
(define (evalo expr val env)
  (conde
    ;; quoted symbols only
    [(symbolo val) (== expr `',val) (¬assoco 'quote env)]
    [(numbero val) (== expr val)]
    [(symbolo expr) (assoco expr val env)]
    ;; set operations
    ;; TODO: multi-element set literals. need eval-listo?
    [(fresh (M N P Q)
       (== expr `(union ,M ,N))
       (evalo M P env)
       (evalo N Q env)
       (uniono P Q val))]
    [(fresh (M V) (== val `(,V)) (== expr `(set ,M)) (evalo M V env))]
    [(== val '()) (== expr `(set))]
    ;; set comprehensions
    [(fresh (x M N MV sets)
       (== expr `(for ((,x ,M)) ,N))
       (evalo M MV env)
       ;; for every x in V, evaluate N. take the union of all results.
       (mapo MV sets (lambda (elem set) (evalo N set `((,x . ,elem) . ,env))))
       (unionso val sets))]
    ;; fixed points
    [(fresh (x M)
       (== expr `(fix (,x) ,M))
       (symbolo x)
       (fixpointo x M '() val env))]
    ;; lambda
    [(fresh (x M env^)
       (== val `(closure ,x ,M ,env))
       (== expr `(lambda (,x) ,M))
       (symbolo x)
       (¬assoco 'lambda env))]
    ;; function application
    [(fresh (M N x O env^ N-val)
       (== expr `(,M ,N))
       (evalo M `(closure ,x ,O ,env^) env)
       (evalo N N-val env)
       (evalo O val `((,x . ,N-val) . ,env^)))]
    ))

(define (fixpointo x M current end env)
  (fresh (next)
    (evalo M next `((,x . ,current) . ,env))
    (conde
      ;; should I use (permuteo current next) instead?
      [(== current next) (== next end)]
      [(=/= next current) (fixpointo x M next end env)])))
