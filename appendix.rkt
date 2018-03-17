#lang racket

(require "fast-mk/mk.rkt")

;; This is the code that went into the appendix of "Experience Report: Rapid
;; Prototyping Language Semantics in miniKanren".
;;
;; Michael Arntzenius, <daekharel@gmail.com>
;; 2018-03-16

;; ---------- General utilities ----------
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

;; ---------- 1. Forward-chaining deduction ----------
;; "The rules for `path`, applied to this database of already known facts, can
;; deduce this fact in one step".
(define (deduce known inferred)
  (fresh (X Y Z)
    (== inferred `(path ,X ,Z))
    (not-membero inferred known) ;; avoid deducing facts we already know.
    (conde
     [(membero `(edge ,X ,Z) known)]
     [(membero `(path ,X ,Y) known)
      (membero `(path ,Y ,Z) known)])))

;; Any number of steps of deduction.
(define (deduce* before after)
  (conde [(== before after)]
         [(fresh (X) (deduce before X) (deduce* (cons X before) after))]))

;; ---------- 2. Stability via list comprehensions ----------
(define (forallo elems pred)
  (conde
   [(== elems '())]
   [(fresh (X Xs)
      (== elems (cons X Xs))
      (pred X)
      (forallo Xs pred))]))

(define-syntax-rule (forall (pred arg ...) known body ...)
  (forallo known
    (lambda (fact)
      (conde
       ;; wrong predicate, ignore
       [(fresh (P X)
          (=/= P 'pred)
          (== fact (cons P X)))]
       ;; the predicate we're looking for
       [(fresh (arg ...)
          (== fact (list 'pred arg ...))
          body ...)]))))

;; "`known` is stable under the rules for `path`"
(define (stable known)
  (fresh ()
    (forall (edge X Y) known
      (membero `(path ,X ,Y) known))
    (forall (path X Y) known
      (forall (path Y2 Z) known
        ;; Note how, here, we have to manually encode the constraint that the Y
        ;; in path(X,Y) and the Y in path(Y,Z) are equal!
        (conde [(=/= Y Y2)]
               [(== Y Y2)
                (membero `(path ,X ,Z) known)])))))

;; Deducing until stability.
(define (deduce-all known known^)
  (conde
   [(== known known^) (stable known)]
   [(fresh (inferred)
      (deduce known inferred)
      (deduce-all (cons inferred known) known^))]))

;; ---------- 3. A relational interpreter for Datalog ----------

;; We take advantage of miniKanren's Turing-completeness, and reimplement
;; unification-with-ground-terms (and its negation!).
;;
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

;; Now we can implement conjunctive queries. A conjunctive query is just a list
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

;; (path-1stepo known deduced) makes `deduced` a list of all facts that may
;; be deduced in one step from the rules for `path` applied to the database
;; `known`.
(define (path-1stepo known deduced)
  (fresh (S1 S2)
    (satisfyo '(path 'X 'Z) '((edge 'X 'Z)) known '() S1)
    (satisfyo '(path 'X 'Z) '((path 'X 'Y) (path 'Y 'Z)) known '() S2)
    (appendo S1 S2 deduced)))

;; Whew! Let's try this:
(define (test-path-1stepo)
  (displayln (run 10 (R) (path-1stepo '((edge a b) (edge b c)) R)))
  (displayln (run 10 (R) (path-1stepo '((path a b) (path b c)) R))))

;; Running (test-path-1stepo) should print:
;;
;; (((path a b) (path b c)))
;; (((path a c)))

;; Now, let's find the "fixed point" of an all-at-once entailment relation like
;; path-1stepo.
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
  (run n (R) ((fixed-point path-1stepo) init-db R)))

;; Final note: in miniKanren any relation can run in any direction. However,
;; there is still a bit of "modedness" about it:
;;
;; - Different directions my have different termination behavior. All directions
;; will be complete (generate all true facts), but only some will know when
;; they're *done* generating facts.
;;
;; - If you are using lists to represent sets or multisets, unless you're very
;; careful in how you write your rules, only certain *orderings* of the set will
;; be produced/accepted by your predicate. path-1stepo is an example: although
;; `deduced` is meant to represent a set, the facts in it must/will occur in a
;; certain *order*.
