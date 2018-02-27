#lang racket

(require "fast-mk/mk.rkt")

;; Some general utilities.
(define (membero elem lst)
  (fresh (X Xs)
    (== lst (cons X Xs))
    (conde [(== X elem)] [(membero elem Xs)])))

;; This file is an exploration of implementing Datalog semantics in miniKanren,
;; in various ways.

;; Let's consider the following Datalog program, my favorite:
;;
;; path(X,Y) :- edge(X,Y).
;; path(X,Z) :- path(X,Y), path(Y,Z).

;; Let's encode the relation "these rules for `path`, with this database of
;; already known facts, can produce this fact in one step":
(define (path-1stepo known inferred)
  (fresh (X Y Z)
    (== inferred `(path ,X ,Z))
    (conde
     [(membero `(edge ,X ,Z) known)]
     [(membero `(path ,X ,Y) known)
      (membero `(path ,Y ,Z) known)])))

;; We can combine multiple rules, deducing anything any of them can deduce, like
;; this:
(define-syntax-rule (combine-rules rule ...)
  (lambda (known inferred)
    (conde [(rule known inferred)] ...)))

;; We can take the "closure" of a rule's consequences, applying it repeatedly to
;; an initial set of known facts to obtain a final database, as follows:
(define ((closure rule) known new-known)
  (conde
   [(== known new-known)]
   [(fresh (Inferred)
      (rule known Inferred)
      ((closure rule) (cons Inferred known) new-known))]))

;; Problem: ((closure rule) known X) is an infinite relation! Nothing stops us
;; repeatedly generating a fact we already know, endlessly expanding the
;; database.
;;
;; We could define not-membero to avoid adding facts we already know; even so,
;; ((closure rule) known X) would remain "nonterminating".
;;
;; We need to determine when /nothing more is deducible/ from a set of rules
;; applied to a set of facts. This is necessary, in particular, to implement
;; negation in Datalog. But it is very difficult to encode in miniKanren.

;; Let's state the problem logically. Suppose we have a relation
;;
;;     entails(database, fact)
;;
;; which holds when any rule in our Datalog program, applied to a `database` of
;; known facts, can deduce `fact` in one step. For example, path-1stepo encodes
;; `entails` for the Datalog program defining `path`.
;;
;; We wish to know if a database is *stable*, defined as follows:
;;
;;   stable(db) :- ∀C. entails(R, db, C) ⊃ member(C, db).
;;
;; But **this is not a Horn clause**!

;; So, although miniKanren is a capable logic programming language, I see no way
;; to reuse its logic-programming features (unification, search) to implement
;; Datalog's logic-programming features.
;;
;; What we *can* do is take advantage of miniKanren's Turing-completeness,
;; and reimplement unification **and its negation** ourselves.
