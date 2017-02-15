(ns latte-integers.core
  "A formalization of the type of integers."

  (:refer-clojure :exclude [and or not int =])

  (:require [latte.core :as latte :refer [defprimitive defaxiom defthm definition
                                          ==> lambda forall
                                          proof try-proof assume have qed]]
            [latte.prop :as p :refer [and or not <=>]]
            [latte.rel :as rel]
            [latte.fun :as fun]
            [latte.quant :as q :refer [exists]]
            [latte.equal :as eq :refer [equal]]
            [latte-sets.core :as set :refer [elem]]))

(defaxiom int
  "The type of integers."
  []
  :type)

(definition =
  "The equality on integers."
  [[n int] [m int]]
  (equal int n m))

(defaxiom zero
  "The integer zero."
  []
  int)

(defaxiom succ
  "The successor integer."
  []
  (==> int int))

(definition one
  "The integer one."
  []
  (succ zero))

(defaxiom succ-bijective
  "The successor function is bijective."
  []
  (fun/bijective int int succ))

(defthm succ-surjective
  "The successor function is surjective."
  []
  (fun/surjective int int succ))

(proof succ-surjective :term
  ((fun/bijective-is-surjective int int succ) succ-bijective))

(defthm succ-injective
  "The successor function is injective."
  []
  (fun/injective int int succ))

(proof succ-injective :term
  ((fun/bijective-is-injective int int succ) succ-bijective))

(defthm succ-ex
  "An integer `y` is the successor of  *at least* another integer."
  [[y int]]
  (exists [x int] (equal int (succ x) y)))

(proof succ-ex :term
  (succ-surjective y))

(defthm succ-single
  "An integer `y` is the successor of *at most* another integer."
  [[y int]]
  (q/single int (lambda [x int] (= (succ x) y))))

(proof succ-single :term
  ((fun/injective-single int int succ)
   succ-injective
   y))
 
(defthm succ-unique
  "There is a unique successor to an integer `y`."
  [[y int]]
  (q/unique int (lambda [x int] (= (succ x) y))))

(proof succ-unique :term
  ((fun/bijective-unique int int succ)
   succ-bijective
   y))

(definition pred
  "The predecessor as the inverse of the successor."
  []
  (fun/inverse int int succ succ-bijective))

(defthm succ-of-pred
  "The succesor of the predecessor of `y` is ... `y`."
  [[y int]]
  (= (succ (pred y)) y))

(proof succ-of-pred
    :term
  ((fun/inverse-prop int int succ succ-bijective)
   y))

(defthm pred-of-succ
  "The predecessor of the successor of `y` is ... `y`."
  [[y int]]
  (= (pred (succ y)) y))

(proof pred-of-succ
    :term
  ((fun/inverse-prop-conv int int succ succ-bijective)
   y))

(defthm pred-bijective
  "The predecessor function is bijective"
  []
  (fun/bijective int int pred))

(proof pred-bijective
    :term
  (fun/inverse-bijective int int succ succ-bijective))

(defthm pred-surjective
  "The predecessor function is surjective."
  []
  (fun/surjective int int pred))

(proof pred-surjective
    :term
  (fun/inverse-surjective int int succ succ-bijective))

(defthm pred-injective
  "The predecessor function is injective"
  []
  (fun/injective int int pred))

(proof pred-injective
    :term
  (fun/inverse-injective int int succ succ-bijective))


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
      (have <b> (and (P (succ x))
                     (P (pred x)))
            :by (Hsp x)))
    (have <c> (forall [x int] (P x))
          :by ((int-induct P) <a> <b>))
    (qed <c>)))

