#lang racket

(require "fast-mk/mk.rkt" "macros.rkt" "lists.rkt")

(define-rules (typeo type) (A B)
  [('num)] [('bool)] [('sym)]
  [(`(,A * ,B))  (typeo A) (typeo B)]
  [(`(,A -> ,B)) (typeo A) (typeo B)])

(define (⊢ term type Γ)
  (matche* (type term) (x A B M N)
   [('num term) (numbero term)]
   [('bool #t)]
   [('bool #f)]
   [('sym `',x) (symbolo x)]
   ;; variables
   [(type term) (symbolo term) (assoco term type Γ)]
   ;; functions
   [(`(,A -> ,B) `(lambda (,x) ,M))
    (symbolo x) (typeo A) (¬assoco 'lambda Γ)
    (⊢ M B `((,x . ,A) . ,Γ))]
   [(B `(,M ,N)) (⊢ M `(,A -> ,B) Γ) (⊢ N A Γ)]
   ;; pairs
   [(`(,A * ,B) `(cons ,M ,N)) (⊢ M A Γ) (⊢ M B Γ) (¬assoco 'cons Γ)]
   [(A `(car ,M))
    (typeo B) ;; <-- do I need this?
    (⊢ M `(,A * ,B) Γ) (¬assoco 'car Γ)]
   [(B `(cdr ,M)) (typeo A) (⊢ M `(,A * ,B) Γ) (¬assoco 'cdr Γ)])
  )
