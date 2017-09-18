#lang racket

;; An implementation of mini-Datafun (WITHOUT types, monotonicity, termination
;; checking, or semilattice types other than finite sets, but WITH fixed points
;; and set comprehensions) in miniKanren.
;;
;; TODO:
;; - typing judgment relation?
;; - booleans & conditionals?
;; - {,in}equality tests?
;; - MORE EXAMPLES!

(require "fast-mk/mk.rkt" "macros.rkt" "lists.rkt" "sets.rkt")

(provide (all-defined-out))

(define (evalo env term val)
  (conde
    ;; quoted symbols only
    [(symbolo val) (== term `',val) (¬assoco 'quote env)]
    [(numbero val) (== term val)]
    [(symbolo term) (assoco term val env)]
    ;; set operations
    [(fresh (Ms Vs)
       (== term `(set ,@Ms))
       (eval-listo env Ms Vs)
       (nubo Vs val))]
    [(fresh (Ms Vs)
       (== term `(union ,@Ms))
       (eval-listo env Ms Vs)
       (ord-unionso val Vs))]
    ;; set comprehensions
    [(fresh (x M N MV sets)
       (== term `(for ((,x ,M)) ,N))
       (evalo env M MV)
       ;; for every x in V, evaluate N. take the union of all results.
       (mapo MV sets (lambda (elem set) (evalo `((,x . ,elem) . ,env) N set)))
       (ord-unionso val sets))]
    ;; fixed points
    [(fresh (x M)
       (== term `(fix (,x) ,M))
       (symbolo x)
       (fixpointo x M '() val env))]
    ;; lambda
    [(fresh (x M env^)
       (== val `(closure ,x ,M ,env))
       (== term `(lambda (,x) ,M))
       (symbolo x)
       (¬assoco 'lambda env))]
    ;; function application
    [(fresh (M N x O env^ N-val)
       (== term `(,M ,N))
       (evalo env M `(closure ,x ,O ,env^))
       (evalo env N N-val)
       (evalo `((,x . ,N-val) . ,env^) O val))]
    ))

(define (eval-listo env terms vals)
  (mapo terms vals (curry evalo env)))

(define (fixpointo x M current end env)
  (fresh (next)
    (evalo `((,x . ,current) . ,env) M next)
    (conde
      [(== current next) (== next end)]
      [(=/= next current) (fixpointo x M next end env)])))

 ;; Types.
(define (hideo Γ Γ^)
  (== Γ^ '()))       ; TODO

;; TODO: MONOTONICITY
(define (⊢ term type Γ)
  (matche* (type term) (x A B M N tone Γ^)
   ;; literals
   [('num term) (numbero term)]
   [('sym `',x) (symbolo x)]
   ;; variables
   [(type term) (symbolo term) (assoco term `(,type ,tone) Γ)]
   ;; set operations
   [(`(set ,A) `(set))]
   [(`(set ,A) `(set ,M)) (hideo Γ Γ^) (⊢ M A Γ^)]
   [(`(set ,A) `(union ,M ,N)) (⊢ M type Γ) (⊢ N type Γ)]
   ;; fixed points
   [(`(set ,A) `(fix (,x) ,M)) (⊢ M type `((,x ,type mono) ,@Γ))]
   ;; lambda & function application
   [(`(,A -> ,B) `(lambda (,x) ,M))
    (symbolo x) (¬assoco 'lambda Γ) (⊢ M B `((,x . ,A) . ,Γ))]
   [(type `(,M ,N)) (⊢ M `(,A -> ,type) Γ) (⊢ N A Γ)]
   ))
