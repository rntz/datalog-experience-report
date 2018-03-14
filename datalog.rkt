#lang racket

(require "fast-mk/mk.rkt")

;; This file is an exploration of implementing Datalog semantics in miniKanren,
;; in various ways.

;; First, some general utilities.
(define (membero elem lst)
  (fresh (X Xs)
    (== lst (cons X Xs))
    (conde [(== X elem)] [(membero elem Xs)])))

;; Let's begin with my favorite Datalog program:
;;
;;     path(X,Z) :- edge(X,Z).
;;     path(X,Z) :- path(X,Y), path(Y,Z).
;;
;; This defines `path` to be the transitive closure of `edge`.

;; Let's encode the relation "the rules for `path`, applied to this database of
;; already known facts, can deduce this fact in one step":
(define (path-1stepo known inferred)
  (fresh (X Y Z)
    (== inferred `(path ,X ,Z))
    (conde
     [(membero `(edge ,X ,Z) known)]
     [(membero `(path ,X ,Y) known)
      (membero `(path ,Y ,Z) known)])))

;; We combine multiple rules, deducing anything any of them can deduce, like so:
(define-syntax-rule (combine-rules rule ...)
  (lambda (known inferred)
    (conde [(rule known inferred)] ...)))

;; We can take the "closure" of a rule's consequences, applying it any number of
;; times to an initial fact-database to obtain a final fact-database, as follows:
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
;;   stable(db) :- ∀fact. entails(db, fact) ⊃ member(fact, db).
;;
;; But **this is not a Horn clause**!

;; So although miniKanren is a capable logic programming language, I see no way
;; to reuse its logic-programming features (unification, in particular) to
;; implement Datalog's logic-programming features.

;; Compiles a single datalog rule to code for a minikanren predicate.
;; TODO: test this!
;; this won't go in paper.
(define (compile-rule conc . premises)
  (define vars '())
  (define (lookup! x)
    (define val (assoc x vars))
    (if val (cdr val)
        (let ((val (gensym x)))
          (set! vars (cons (cons x val) vars))
          val)))
  (define (compile-argument arg)
    (if (symbol? arg) (lookup! arg) arg))
  (define (compile-atom atom)
    `(list ',(car atom) ,@(map compile-argument (cdr atom))))
  (define conc (compile-atom conc))
  (define premises (map compile-atom premises))
  `(lambda (known inferred)
     (fresh ,(map cdr vars)
        (== inferred ,conc)
        ,@(map (lambda (premise) `(membero ,premise known)) premises))))

(define (compile-rules rules)
  `(closure (combine-rules ,@(map compile-rule rules))))
