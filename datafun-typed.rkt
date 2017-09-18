#lang racket

;; A typed evaluation relation. I'm not sure this is a good idea; perhaps it's
;; better to separately having a typing relation and an evaluation relation.

(require "fast-mk/mk.rkt" "macros.rkt" "lists.rkt" "sets.rkt")

(provide (all-defined-out))

(define-rules (typeo type) (A B)
  [('num)] [('bool)] [('sym)]
  [(`(set ,A)) (typeo A)]
  [(`(,A * ,B))  (typeo A) (typeo B)]
  [(`(,A -> ,B)) (typeo A) (typeo B)])

;; TODO: a cool idea: pass a list of typing rules that may be used as an
;; auxiliary argument. this allows us to dynamically say what sub-language we
;; want to generate terms in.

;; I think the constant use of typeo here is slowing us down. Really we want
;; typeo to be a constraint, not a predicate.
(define (evalo env term type val)
  (conde
   ;; variables
   [(symbolo term) (assoco term `(,type ,val) env)]
   ;; literals
   [(== type 'sym) (symbolo val) (== term `',val) (¬assoco 'quote env)]
   [(== type 'num) (numbero val) (== term val)]
   ;; set operations
   [(fresh (A) (== type `(set ,A))
      (conde
       [(== term `(set)) (== val '()) (typeo A)]
       [(fresh (M MV) (== term `(set ,M)) (== val  `(,MV)) (evalo env M A MV))]
       [(fresh (M N MV NV)
          (== term `(union ,M ,N))
          (evalo env M type MV)
          (evalo env N type NV)
          (uniono MV NV val))]
       ;; set comprehensions
       [(fresh (x M N MA MV sets)
          (== term `(for ((,x ,M)) ,N))
          (evalo env M `(set ,MA) MV)
          (mapo MV sets (lambda (elem set) (evalo `((,x ,MA ,elem) ,@env) N type set)))
          (unionso val sets)
          (typeo MA))]
       ;; TODO: fixed points
       ))]
   ;; pairs
   [(fresh (A B M N MV NV)
      (== type `(,A * ,B))
      (== term `(cons ,M ,N)) (¬assoco 'cons env)
      (== val  (cons MV NV))
      (evalo env M A MV)
      (evalo env N B NV))]
   [(fresh (B M ignored)
      (== term `(car ,M)) (¬assoco 'car env)
      (evalo env M `(,type * ,B) `(,val . ,ignored))
      (typeo B))]
   [(fresh (A M ignored)
      (== term `(cdr ,M)) (¬assoco 'cdr env)
      (evalo env M `(,A * ,type) `(,ignored . ,val))
      (typeo A))]
   ;; lambda
   [(fresh (A B x M)
      (== type `(,A -> ,B))
      (== term `(lambda (,x) ,M)) (¬assoco 'lambda env)
      (== val  `(closure ,x ,M ,env))
      (typeo A) (symbolo x))]
   ;; function application
   [(fresh (A M N x O env^ N-val)
      (== term `(,M ,N))
      (evalo env M `(,A -> ,type) `(closure ,x ,O ,env^))
      (evalo env N A N-val)
      (evalo `((,x ,A ,N-val) ,@env^) O type val))]
   ))
