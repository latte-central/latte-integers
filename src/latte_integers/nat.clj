(ns latte-integers.nat
  "The natural integers in ℕ as a subset of ℤ."

  (:refer-clojure :exclude [and or not int])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          lambda forall proof assume have
                                          ==>]])

  (:require [latte.prop :as p :refer [and or not <=>]])

  (:require [latte.equal :as eq :refer [equal]])

  (:require [latte-integers.core :as int :refer [zero succ pred int]])

  (:require [latte-sets.core :as set :refer [elem]])

  )

(definition nat-succ-prop
  "A property verified by all successors of natural integers."
  [[P (==> int :type)]]
  (forall [y int] (==> (P y) (P (succ y)))))

(definition nat
  "The subset of natural integers."
  []
  (lambda [x int]
    (forall [P (==> int :type)]
      (==> (and (P zero)
                (nat-succ-prop P))
           (P x)))))

(defthm nat-zero
  "Zero is a natural integer."
  []
  (elem int zero nat))

(proof nat-zero :script
  (assume [P (==> int :type)
           H (and (P zero)
                  (nat-succ-prop P))]
    (have a (P zero) :by (p/%and-elim-left H))
    (qed a)))

(defthm nat-succ
  "The successor of a natural integer is a natural integer."
  [[x int]]
  (==> (elem int x nat)
       (elem int (succ x) nat)))

(proof nat-succ :script
  (assume [H (elem int x nat)]
    (assume [Q (==> int :type)
             H2 (and (Q zero)
                     (nat-succ-prop Q))]
      (have a (==> (and (Q zero)
                        (nat-succ-prop Q))
                   (Q x)) :by (H Q))
      (have b (Q x) :by (a H2))
      (have c (==> (Q x) (Q (succ x)))
            :by ((p/%and-elim-right H2) x))
      (have d (Q (succ x)) :by (c b))
      (qed d))))

(defaxiom nat-zero-has-no-pred
  "An important axiom of the natural integer subset
wrt. [[pred]]."
  []
  (not (elem int (pred zero) nat)))

(defthm nat-zero-is-not-succ
  "Zero is not a successor of a natural integer.

This is the first Peano 'axiom' (here theorem, based
 on integers) for natural integers."
  []
  (forall [x int]
    (==> (elem int x nat)
         (not (equal int (succ x) zero)))))

(proof nat-zero-is-not-succ :script
  (assume [x int
           H (elem int x nat)]
    (assume [H2 (equal int (succ x) zero)]
      (have a (equal int (pred (succ x)) (pred zero))
            :by ((eq/eq-cong int int pred (succ x) zero) H2))
      (have b (equal int x (pred (succ x)))
            :by ((eq/eq-sym int (pred (succ x)) x)
                 (int/pred-of-succ x)))
      (have c (equal int x (pred zero))
            :by ((eq/eq-trans int x (pred (succ x)) (pred zero))
                 b a))
      (have d (elem int (pred zero) nat)
            :by ((eq/eq-subst int nat x (pred zero))
                 c H))
      (have e p/absurd :by (nat-zero-has-no-pred d))
      (qed e))))

(defthm nat-succ-injective
  "Successor is injective, the second Peano 'axiom'
here a simple consequence of [[succ-injective]]."
  []
  (forall [x y int]
    (==> (elem int x nat)
         (elem int y nat)
         (equal int (succ x) (succ y))
         (equal int x y))))

(proof nat-succ-injective :script
  (assume [x int
           y int
           H1 (elem int x nat)
           H2 (elem int y nat)
           H3 (equal int (succ x) (succ y))]
    (have a (equal int x y)
          :by (int/succ-injective x y H3))
    (have b _ :discharge [H1 H2 H3 a])
    (qed b)))

(defthm nat-induct
  "The induction principle for natural integers.
This is the third Peano axiom but it can be
derived from [[int-induct]]."
  [[P (==> int :type)]]
  (==> (and (P zero)
            (forall [x int]
              (==> (elem int x nat)
                   (P x)
                   (P (succ x)))))
       (forall [x int]
         (==> (elem int x nat)
              (P x)))))

(proof nat-induct :script
  (have Q _ :by (lambda [z int]
                  (and (elem int z nat)
                       (P z))))
  (assume [u (and (P zero)
                  (forall [x int]
                    (==> (elem int x nat)
                         (P x)
                         (P (succ x)))))]
    (have a (P zero) :by (p/%and-elim-left u))
    (have b (forall [x int]
              (==> (elem int x nat)
                   (P x)
                   (P (succ x))))
          :by (p/%and-elim-right u))
    (have c (Q zero) :by ((p/and-intro (elem int zero nat)
                                       (P zero))
                          nat-zero a))
    (assume [y int
             v (Q y)]
      (have d (elem int y nat)
            :by (p/%and-elim-left v))
      (have e (P y)
            :by (p/%and-elim-right v))
      (have f (elem int (succ y) nat)
            :by ((nat-succ y) d))
      (have g (==> (P y) (P (succ y)))
            :by (b y d))
      (have h (P (succ y)) :by (g e))
      (have i (Q (succ y)) :by ((p/and-intro (elem int (succ y) nat)
                                             (P (succ y)))
                                f h))
      (have j (nat-succ-prop Q) :discharge [y v i]))
    (have k (and (Q zero)
                 (nat-succ-prop Q)) :by ((p/and-intro (Q zero)
                                                      (nat-succ-prop Q)) c j))
    (assume [x int
             w (elem int x nat)]
      (have l (Q x) :by (w Q k))
      (have m (P x) :by (p/%and-elim-right l))
      (have n (forall [x int]
                (==> (elem int x nat)
                     (P x))) :discharge [x w m])
      (qed n))))


