#lang racket

(require "fast-mk/mk.rkt")

;; This file is an exploration of implementing Datalog semantics in miniKanren,
;; in various ways.

;; First, some general utilities.
(define (membero elem lst)
  (fresh (X Xs)
    (== lst (cons X Xs))
    (conde [(== X elem)] [(=/= X elem) (membero elem Xs)])))

(define (not-membero elem lst)
  (conde
   [(== lst '())]
   [(fresh (X Xs)
      (=/= elem X)
      (== lst (cons X Xs))
      (not-membero elem Xs))]))

;; Some more specific utilities.
(define (forallo elems pred)
  (conde
   [(== elems '())]
   [(fresh (X Xs)
      (== elems (cons X Xs))
      (pred X)
      (forallo Xs pred))]))

(define-syntax-rule (forall-facts known pred (arg ...) body ...)
  (forallo known
    (lambda (fact)
      (conde
       ;; wrong predicate, ignore
       [(fresh (P X)
          (=/= P pred)
          (== fact (cons P X)))]
       ;; the predicate we're looking for
       [(fresh (arg ...)
          (== fact (list pred arg ...))
          body ...)]))))

;; Let's begin with my favorite Datalog program:
;;
;;     path(X,Z) :- edge(X,Z).
;;     path(X,Z) :- path(X,Y), path(Y,Z).
;;
;; This defines `path` to be the transitive closure of `edge`.

;; Let's encode the relation "the rules for `path`, applied to this database of
;; already known facts, can deduce this fact in one step":
(define (deduce known inferred)
  (fresh (X Y Z)
    (== inferred `(path ,X ,Z))
    (not-membero inferred known)
    (conde
     [(membero `(edge ,X ,Z) known)]
     [(membero `(path ,X ,Y) known)
      (membero `(path ,Y ,Z) known)])))

;; "`known` is stable under the rules for `path`"
(define (stable known)
  (fresh ()
    (forall-facts known 'edge (X Y)
      (membero `(path ,X ,Y) known))
    (forall-facts known 'path (X Y)
      (forall-facts known 'path (Y2 Z)
        (conde
         ;; Note how, here, we have to manually encode the constraint that the Y
         ;; in path(X,Y) and the Y in path(Y,Z) are equal!
         [(=/= Y Y2)]
         [(== Y Y2) (membero `(path ,X ,Z) known)])))))

;; And now, Datalog!
(define (deduce-all known known^)
  (conde
   [(== known known^)
    (stable known)]
   [(fresh (inferred)
      (deduce known inferred)
      (deduce-all (cons inferred known) known^))]))
