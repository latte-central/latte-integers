(ns latte-integers.int
  "A formalization of the type of integers."

  (:refer-clojure :exclude [and or not int =])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          lambda forall
                                          proof try-proof assume have qed]]
            [latte.utils :as u]
            [latte-prelude.prop :as p :refer [and or not <=>]]
            [latte-prelude.fun :as fun]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-sets.set :as set :refer [elem]]))

(defaxiom int
  "The type of integers."
  []
  :type)

(definition =
  "The equality on integers."
  [[n int] [m int]]
  (eq/equal n m))

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
  (fun/bijective succ))

(defthm succ-surjective
  "The successor function is surjective."
  []
  (fun/surjective succ))

(proof 'succ-surjective
  (qed ((fun/bijective-is-surjective succ) succ-bijective)))

(defthm succ-injective
  "The successor function is injective."
  []
  (fun/injective succ))

(proof 'succ-injective
  (qed ((fun/bijective-is-injective succ) succ-bijective)))

(defthm succ-ex
  "An integer `y` is the successor of  *at least* another integer."
  [[y int]]
  (exists [x int] (= (succ x) y)))

(proof 'succ-ex
  (qed (succ-surjective y)))

(defthm succ-single
  "An integer `y` is the successor of *at most* another integer."
  [[y int]]
  (q/single (lambda [x int] (= (succ x) y))))

(proof 'succ-single
  (qed ((fun/injective-single succ)
        succ-injective
        y)))
 
(defthm succ-unique
  "There is a unique successor to an integer `y`."
  [[y int]]
  (q/unique  (lambda [x int] (= (succ x) y))))

(proof 'succ-unique
  (qed ((fun/bijective-unique succ)
        succ-bijective
        y)))

(definition pred
  "The predecessor as the inverse of the successor."
  []
  (fun/inverse succ succ-bijective))

(defthm succ-of-pred
  "The succesor of the predecessor of `y` is ... `y`."
  [[y int]]
  (= (succ (pred y)) y))

(proof 'succ-of-pred   
  (qed ((fun/inverse-prop succ succ-bijective)
        y)))

(defthm pred-of-succ
  "The predecessor of the successor of `y` is ... `y`."
  [[y int]]
  (= (pred (succ y)) y))

(proof 'pred-of-succ
    (qed
     ((fun/inverse-prop-conv succ succ-bijective)
      y)))

(defthm pred-bijective
  "The predecessor function is bijective"
  []
  (fun/bijective pred))

(proof 'pred-bijective
    (qed
     (fun/inverse-bijective succ succ-bijective)))

(defthm pred-surjective
  "The predecessor function is surjective."
  []
  (fun/surjective pred))

(proof 'pred-surjective
    (qed
     (fun/inverse-surjective succ succ-bijective)))

(defthm pred-injective
  "The predecessor function is injective"
  []
  (fun/injective pred))

(proof 'pred-injective
    (qed
     (fun/inverse-injective succ succ-bijective)))

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

(proof 'int-case
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
            :by ((int-induct P) <a> <b>)))
  (qed <c>))

;; predecessor is opaque
(u/set-opacity! #'pred true)
