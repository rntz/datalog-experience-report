#lang racket

;; Coding up "stability" of a database under a set of datalog rules in
;; miniKanren. It took many tries to figure this out.

(require "fast-mk/mk.rkt")

(define (membero elem lst)
  (fresh (X Xs)
    (== lst (cons X Xs))
    (conde [(== X elem)] [(=/= X elem) (membero elem Xs)])))

;; Consider the Datalog program:
;;
;;     path(X,Y) :- edge(X,Y).
;;     path(X,Z) :- path(X,Y), path(Y,Z).
;;
;; This defines `path` to be the transitive closure of `edge`.
;;
;; Given a database (i.e. a list) of facts `known`, we wish to know: is this
;; database *stable*? That is, for each Datalog rule above, are all of its
;; consequences when applied to this database ALREADY IN the database?

;; Here's the shortest I've been able to make this code. I've heard Will Byrd
;; doesn't like to use "forallo" or macros, but doing this all directly just
;; feels awful.
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

;; Now we can define what it is to be stable under each of the two rules above.
;; First, stability under "path(X,Y) :- edge(X,Y)."
(define (edge-stable known)
  (forall-facts known 'edge (X Y)
    (membero `(path ,X ,Y) known)))

;; Now, stability under "path(X,Z) :- path(X,Y), path(Y,Z)."
(define (path-stable known)
  (forall-facts known 'path (X Y)
    (forall-facts known 'path (Y2 Z)
      (conde
       ;; Note how, here, we have to manually encode the constraint that the Y
       ;; in path(X,Y) and the Y in path(Y,Z) are equal!
       [(=/= Y Y2)]
       [(== Y Y2) (membero `(path ,X ,Z) known)]))))
