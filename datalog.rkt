#lang racket

(require "fast-mk/mk.rkt")

;; This file is an exploration of implementing Datalog semantics in miniKanren,
;; in various ways.

;; First, some general utilities.
(define (membero elem lst)
  (fresh (X Xs)
    (== lst (cons X Xs))
    (conde [(== X elem)] [(membero elem Xs)])))

(define (not-membero elem lst)
  (conde
   [(== lst '())]
   [(fresh (X Xs)
      (=/= elem X)
      (== lst (cons X Xs))
      (not-membero elem Xs))]))

(define (assoco key val lst)
  (membero (cons key val) lst))

(define (not-assoco key lst)
  (conde
   [(== lst '())]
   [(fresh (K V Rest)
      (=/= key K)
      (== lst (cons (cons K V) Rest))
      (not-assoco key Rest))]))

(define (appendo x y xy)
  (conde
   [(== x '()) (== y xy)]
   [(fresh (X X-rest XY-rest)
      (== x (cons X X-rest))
      (== xy (cons X XY-rest))
      (appendo X-rest y XY-rest))]))

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


;; What we *can* do is take advantage of miniKanren's Turing-completeness, and
;; reimplement unification-with-ground-terms **and its negation** ourselves.
;; With these, we can finally implement `stable`.

;; Unification variables X are represented by quotations: (quote X).
;; Ground terms have no subterms of the form (quote X).
;; Substitutions always map variables to fully ground terms.
(define (unifyo schema ground subst-in subst-out)
  (conde
   [(== subst-in subst-out)
    (conde [(== schema ground)]
           [(=/= schema ground)
            (fresh (X)
              (== schema `',X)
              (assoco X ground subst-in))])]
   [(fresh (X)
      (== schema (list 'quote X))
      (not-assoco X subst-in)
      (== subst-out `((,X . ,ground) . ,subst-in)))]
   [(fresh (Xl Xr Gl Gr S)
      (=/= Xl 'quote)
      (== schema (cons Xl Xr))
      (== ground (cons Gl Gr))
      (unifyo Xl Gl subst-in S)
      (unifyo Xr Gr S subst-out))]))

(define (not-unifyo schema ground subst)
  (conde
   ;; unequal symbols don't unify.
   [(symbolo schema) (symbolo ground) (=/= schema ground)]
   ;; a variable mapped to an unequal ground won't unify.
   [(fresh (X G) (=/= G ground) (== schema `',X) (assoco X G subst))]
   ;; if one is a symbol & the other is a cons, they can't unify.
   [(fresh (X Y)
      (conde
       [(symbolo schema) (== ground (cons X Y))]
       [(symbolo ground) (== schema (cons X Y)) (=/= X 'quote)]))]
   ;; if they're both conses, it gets complicated.
   [(fresh (Xl Xr Gl Gr)
      (=/= Xl 'quote)
      (== schema (cons Xl Xr))
      (== ground (cons Gl Gr))
      (conde
       [(not-unifyo Xl Gl subst)]
       [(fresh (S) (unifyo Xl Gl subst S) (not-unifyo Xr Gr S))]))]))

(define (substo subst schema ground)
  (conde
   [(== schema '()) (== ground '())]
   [(symbolo schema) (== schema ground)]
   [(fresh (X)
      (== schema `',X)
      (assoco X ground subst))]
   [(fresh (Xl Xr Gl Gr)
      (=/= Xl 'quote)
      (== schema (cons Xl Xr))
      (== ground (cons Gl Gr))
      (substo subst Xl Gl)
      (substo subst Xr Gr))]))

;; Now, we can implement conjunctive queries. A conjunctive query is just a list
;; of schemas which we wish to unify with facts in the database. For example,
;;
;;     ((path 'X 'Y) (path 'Y 'Z))
;;
;; is a conjunctive query (remembering that 'X, 'Y, 'Z are how we represent
;; query variables).
;;
;; Running a query against a database gives us a list of substitutions for its
;; variables. We represent substitutions with association-lists. For example,
;; running the query above against the database
;;
;;     ((path a b) (path b c1) (path b c2))
;;
;; would yield two satisfying substitutions, namely:
;;
;;     (((X . a) (Y . b) (Z . c1))
;;      ((X . a) (Y . b) (Z . c2)))
;;
;; For implementing Datalog, it will be convenient if rather than getting the
;; substitutions directly, we instead immediately apply the substitutions to a
;; "result" schema, and return these forms. For example, with the result schema
;; (path 'X 'Z), our query would produce the results:
;;
;;     ((path a c1) (path a c2))

;; (satisfyo result query database subst-in results) holds if running `query`
;; against the facts in `database`, extending the substitution `subst-in`,
;; applying the satisfying substitutions to the schema `result`, produces the
;; ground terms in `results`.
(define (satisfyo result query database subst-in results)
  (define (searcho schema rest-of-query facts subst-in results)
    (conde
     [(== facts '()) (== results '())]
     [(fresh (F Fs)
        (== facts (cons F Fs))
        (conde
         ;; if F doesn't match, continue. NB. this is why we need not-unifyo.
         [(not-unifyo schema F subst-in)
          (searcho schema rest-of-query Fs subst-in results)]
         ;; if F does match...
         [(fresh (S S-out1 S-out2)
            (unifyo schema F subst-in S)
            (satisfyo result rest-of-query database S S-out1)
            (searcho schema rest-of-query Fs subst-in S-out2)
            (appendo S-out1 S-out2 results))]))]))
  (conde
   ;; the trivial query is trivially satisfied
   [(== query '())
    (fresh (R)
     (substo subst-in result R)
     (== results (list R)))]
   ;; otherwise, do a recursive search, starting with the first schema in the
   ;; conjunctive query.
   [(fresh (schema rest-of-query)
      (== query (cons schema rest-of-query))
      (searcho schema rest-of-query database subst-in results))]))

;; Now, finally, we can encode Datalog rules into miniKanren in a way that finds
;; *all* their consequences, without infinitely looping, because it knows when
;; to stop.
;;
;; (path-deduce-allo known deduced) makes `deduced` a list of all facts that may
;; be deduced in one step from the rules for `path` applied to the database
;; `known`.
(define (path-1step-allo known deduced)
  (fresh (S1 S2)
    (satisfyo '(path 'X 'Z) '((edge 'X 'Z)) known '() S1)
    (satisfyo '(path 'X 'Z) '((path 'X 'Y) (path 'Y 'Z)) known '() S2)
    (appendo S1 S2 deduced)))

;; Whew! Let's try this:
(define (test-path-1step-allo)
  (displayln (run 10 (R) (path-1step-allo '((edge a b) (edge b c)) R)))
  (displayln (run 10 (R) (path-1step-allo '((path a b) (path b c)) R))))

;; Running (test-path-1step-allo) should print:
;;
;; (((path a b) (path b c)))
;; (((path a c)))

;; Now, let's find the "fixed point" of an all-at-once entailment relation like
;; path-1step-allo.
(define ((fixed-point rule) current-db stable-db)
  (fresh (deduced)
   (rule current-db deduced)
   (conde
    [(subseto deduced current-db) (== current-db stable-db)]
    [(not-subseto deduced current-db)
     (fresh (next-db)
       (updateo deduced current-db next-db)
       ((fixed-point rule) next-db stable-db))])))

;; We need some helpers here:
;; (subseto small big) holds if everything in `small` is in `big`.
(define (subseto small big)
  (conde
   [(== small '())]
   [(fresh (X Rest)
      (== small (cons X Rest))
      (membero X big)
      (subseto Rest big))]))

(define (not-subseto small big)
  (fresh (X)
   (membero X small)
   (not-membero X big)))

;; (updateo new old updated) inserts everything in `new` into `old`, producing
;; `updated`. If anything in `new` is already in `old`, it avoids inserting it
;; again.
(define (updateo new old updated)
  (conde
   [(== new '()) (== old updated)]
   [(fresh (X Xs)
      (== new (cons X Xs))
      (conde
       [(membero X old) (updateo Xs old updated)]
       [(not-membero X old)
        (fresh (Rest)
          (== updated (cons X Rest))
          (updateo Xs old Rest))]))]))

;; Now, let's test it!
(define (test [n 2])
  (define init-db '((edge a b) (edge b c)))
  (run n (R) ((fixed-point path-1step-allo) init-db R)))

;; Final note: in miniKanren any relation can run in any direction. However,
;; there is still a bit of "modedness" about it:
;;
;; - Different directions my have different termination behavior. All directions
;; will be complete (generate all true facts), but only some will know when
;; they're *done* generating facts.
;;
;; - If you are using lists to represent sets or multisets, unless you're very
;; careful in how you write your rules, only certain *orderings* of the set will
;; be produced/accepted by your predicate. path-1step-allo is an example:
;; although `deduced` is meant to represent a set, the facts in it must/will
;; occur in a certain *order*.
