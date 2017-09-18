#lang racket

(require "fast-mk/mk.rkt" "macros.rkt" "lists.rkt")

(provide permuteo remove-allo nubo nodupso subseto nub==
         ord-uniono uniono unionso ord-unionso
         set-addo)

(define (permuteo X Y)
  (fresh () (length== X Y) (permute-helper X Y)))

(define-rules (permute-helper X Y) (x xs y ys xs^ ys^)
  [('() '())]
  ;; a small optimization.
  [((cons x xs) (cons x ys)) (permute-helper xs ys)]
  [((cons x xs) (cons y ys))
   (=/= x y)
   (rembero x ys ys^)
   (rembero y xs xs^)
   (permute-helper xs^ ys^)])

;; "L-sans-X is L without any Xes."
(define-rules (remove-allo X L L-sans-X) (y ys ys^)
  [(X '() '())]
  [(X (cons X ys) L-sans-X) (remove-allo X ys L-sans-X)]
  [(X (cons y ys) (cons y ys^)) (=/= X y) (remove-allo X ys ys^)])

;; "Y is X with only the first instance of each duplicate kept."
(define-rules (nubo X Y) (x xs xs^ ys)
  [('() '())]
  [((cons x xs) (cons x ys))
   (remove-allo x xs xs^)
   (nubo xs^ ys)])

;; a list has no duplicates iff its nub is itself.
;; ;; uh-oh, this predicate has dangerous termination behavior!
;; (define (nodupso X) (nubo X X))

;; another version of nodupso.
(define-rules (nodupso X) (x xs)
  [('())]
  [((cons x xs)) (nodupso xs) (¬membero x xs)])

;; subseto and nub== work perfectly well (in either direction) if you care about
;; *all* lists representing a set. but if you care about only duplicate-free
;; lists, they can lead to nontermination.
(define (subseto A B) (forallo A (lambda (x) (membero x B))))
(define (nub== A B) (fresh (X Y) (nubo A X) (nubo B Y) (permuteo X Y)))

;; ;; a different definition. probably slower? TODO: test.
;; (define (nub==2 A B) (fresh () (subseto A B) (subseto B A)))

 ;; Operations on sets-without-duplicates.

;; Order-preserving union, AB == nub (A ++ B).
(define (ord-uniono A B AB)
  (fresh (A++B)
   (length<= A AB) (length<= B AB)
   (appendo A B A++B)
   (nubo A++B AB)
   (nodupso A) (nodupso B) ;; ugh
   ))

(module+ test
  (define (FAILURE)
    (run 10 (X Y XY) (length<= XY '(a)) (ord-uniono X Y XY))))

;; Arbitrary union.
;; It's annoying that this duplicates code with ord-uniono.
;; But it seems to be the only way to get the right termination behavior.
(define (uniono A B AB)
  (fresh (A++B A++B^)
   (length<= A AB) (length<= B AB)
   (appendo A B A++B)
   ;; TODO: play around with this. are there other definitions with the right
   ;; behavior?
   (permuteo A++B A++B^)
   (nubo A++B^ AB)
   (nodupso A) (nodupso B)))

(module+ tests
  (define (test-ord-uniono)
    (list
     (run 10 (X Y XY) (length<= XY '(a)) (ord-uniono X Y XY))
     (run 10 (X Y XY) (length<= X '(a)) (length<= Y '(a)) (ord-uniono X Y XY))))

  ;; PROBLEM CASE.
  ;;
  ;; I'm not sure whether there's anything I can do here.
  (define (failing-test-ord-uniono)
    ;; works fine for N < 8. at N = 8, appears to loop.
    (run 7 (X Y Z XY) (ord-uniono X Y XY) (ord-uniono XY Z '(a))))

  (define (test-uniono)
    (list
     (run 10 (X Y XY) (length<= XY '(a)) (uniono X Y XY))
     (run 10 (X Y XY) (length<= X '(a)) (length<= Y '(a)) (uniono X Y XY)))))

;; takes the union of a list of sets. I've only examined the behavior of this
;; running forward, i.e. where `sets` is ground.
(define (unionso X sets)
  (fresh (X^)
    (ord-unionso X^ sets)
    (permuteo X^ X)))

;; this seems to work running forward or backward, as long as `sets` is
;; length-bounded.
(define (ord-unionso X sets)
  (fresh (elems)
   (foralle s sets (length<= s X) (nodupso s))
   (concato sets elems)
   (nubo elems X)))

(module+ test
  (define (test-ord-unionso)
    (= 7 (length (run 8 (X Y Z) (ord-unionso '(a) (list X Y Z)))))))

(define (set-addo X S X+S)
  (conde
   [(membero X S) (== S X+S)]
   [(¬membero X S) (inserto X S X+S)]))
