(ns latte-integers.core
  "A formalization of the type of integers."

  (:refer-clojure :exclude [and or not int])

  (:require [latte.core :as latte :refer [defprimitive defaxiom defthm definition
                                          ==> lambda forall
                                          proof assume have qed]]
            [latte.prop :as p :refer [and or not <=>]]
            [latte.rel :as rel]
            [latte.quant :as q :refer [exists]]
            [latte.equal :as eq :refer [equal]]
            [latte-sets.core :as set :refer [elem]]))

(defaxiom int
  "The type of integers."
  []
  :type)

(defaxiom zero
  "The integer zero."
  []
  int)

(defaxiom succ
  "The successor integer."
  []
  (==> int int))

(defaxiom succ-bijective
  "The successor function is bijective."
  []
  (rel/bijective int int succ))

(defthm succ-surjective
  "The successor function is surjective."
  []
  (rel/surjective int int succ))

(proof succ-surjective :term
  ((rel/bijective-is-surjective int int succ) succ-bijective))

(defthm succ-injective
  "The successor function is injective."
  []
  (rel/injective int int succ))

(proof succ-injective :term
  ((rel/bijective-is-injective int int succ) succ-bijective))

(defthm ex-succ
  "An integer `y` is the successor of  *at least* another integer."
  [[y int]]
  (exists [x int] (equal int (succ x) y)))

(proof ex-succ :term
  (succ-surjective y))

(defthm single-succ
  "An integer `y` is the successor of *at most* another integer."
  [[y int]]
  (q/single int (lambda [x int] (equal int (succ x) y))))

(proof single-succ :script
  (assume [x1 int
           x2 int
           H1 (equal int (succ x1) y)
           H2 (equal int (succ x2) y)]
    (have a (equal int y (succ x2)) :by ((eq/eq-sym int (succ x2) y) H2))
    (have b (equal int (succ x1) (succ x2))
          :by ((eq/eq-trans int (succ x1) y (succ x2))
               H1 a))
    (have c (equal int x1 x2) :by (succ-injective x1 x2 b))
    (qed c)))

(defthm unique-succ
  "There is a unique successor to an integer `y`."
  [[y int]]
  (q/unique int (lambda [x int] (equal int (succ x) y))))

(proof unique-succ :term
  ((p/and-intro (q/ex int (lambda [x int] (equal int (succ x) y)))
     (q/single int (lambda [x int] (equal int (succ x) y))))
   (ex-succ y)
   (single-succ y)))

(definition pred
  "The predecessor of `y`."
  [[y int]]
  (q/the int
         (lambda [x int] (equal int (succ x) y)) 
         (unique-succ y)))

(defthm succ-of-pred
  "The succesor of the predecessor of `y` is ... `y`."
  [[y int]]
  (equal int (succ (pred y)) y))

(proof succ-of-pred :term
  (q/the-prop int (lambda [x int] (equal int (succ x) y)) (unique-succ y)))

(defthm pred-of-succ
  "The predecessor of the successor of `y` is ... `y`."
  [[y int]]
  (equal int (pred (succ y)) y))

(proof pred-of-succ :script
  (have a (equal int (succ (pred (succ y))) (succ y))
        :by (succ-of-pred (succ y)))
  (have b (equal int (pred (succ y)) y)
        :by (succ-injective (pred (succ y)) y a))
  (qed b))

(defaxiom int-induct
  "The induction principle for integers
(as an axiom)."
  [[P (==> int :type)]]
  (==> (P zero)
       (forall [x int] (==> (P x)
                            (and (P (succ x))
                                 (P (pred x)))))
       (forall [x int] (P x))))


(defthm int-case
  "Case analysis for integers."
  [[P (==> int :type)]]
  (==> (P zero)
       (forall [x int] (and (P (succ x))
                            (P (pred x))))
       (forall [x int] (P x))))

(proof int-case
    :script
  (assume [Hz (P zero)
           Hsp (forall [x int] (and (P (succ x))
                                    (P (pred x))))]
    (have <a> (P zero) :by Hz)
    (assume [x int
             Hx (P x)]
      (have <b1> (and (P (succ x))
                     (P (pred x)))
            :by (Hsp x))
      (have <b> (forall [x int] (==> (P x)
                                     (and (P (succ x))
                                          (P (pred x)))))
            :discharge [x Hx <b1>]))
    (have <c> (forall [x int] (P x))
          :by ((int-induct P) <a> <b>))
    (qed <c>)))

