
(ns latte-integers.minus
  "The subtraction (and opposite) defined on ℤ."

  (:refer-clojure :exclude [and or not int = + -])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          try-proof ==>]]

            [latte.prop :as p :refer [and or not <=>]]
            [latte.equal :as eq :refer [equal]]
            [latte.quant :as q :refer [exists]]
            [latte.fun :as fun]

            [latte-sets.core :as set :refer [elem forall-in]]

            [latte-integers.core :as int :refer [zero succ pred int =]]
            [latte-integers.nat :as nat :refer [nat positive negative]]
            [latte-integers.rec :as rec]
            [latte-integers.plus :as plus :refer [+]]))

(deflemma minus-ex
  []
  (forall [n m int]
    (exists [p int] (= (+ p m) n))))

(proof minus-ex
    :script
  (assume [n int]
    "We proceed by induction on `m`."
    "Base case: is `m` is `zero`."
    (have <a1> (= (+ n zero) n)
          :by (plus/plus-zero n))
    (have <a> (exists [p int] (= (+ p zero) n))
          :by ((q/ex-intro int
                           (lambda [p int] (= (+ p zero) n))
                           n)
               <a1>))
    "Now the inductive cases"
    (assume [m int
             Hind (exists [p int] (= (+ p m) n))]
      "First the case for `succ`."
      (assume [p int
               Hp (= (+ p m) n)]
        (have <b1> (= (+ p m) (+ (pred p) (succ m)))
              :by (eq/eq-sym% (plus/plus-pred-succ p m)))
        (have <b2> (= (+ (pred p) (succ m)) n)
              :by (eq/eq-subst% (lambda [k int] (= k n))
                                <b1> Hp))
        (have <b3> (exists [p int] (= (+ p (succ m)) n))
              :by ((q/ex-intro int
                               (lambda [p int] (= (+ p (succ m)) n))
                               (pred p))
                   <b2>))
        "Second the case for `pred`."
        (have <c1> (= (+ p m) (+ (succ p) (pred m)))
              :by (eq/eq-sym% (plus/plus-succ-pred p m)))
        (have <c2> (= (+ (succ p) (pred m)) n)
              :by (eq/eq-subst% (lambda [k int] (= k n))
                                <c1> Hp))
        (have <c3> (exists [p int] (= (+ p (pred m)) n))
              :by ((q/ex-intro int
                               (lambda [p int] (= (+ p (pred m)) n))
                               (succ p))
                   <c2>)))
      (have <d1> (exists [p int] (= (+ p (succ m)) n))
            :by ((q/ex-elim int
                            (lambda [p int] (= (+ p m) n))
                            (exists [p int] (= (+ p (succ m)) n)))
                 Hind <b3>))
      (have <d2> (exists [p int] (= (+ p (pred m)) n))
            :by ((q/ex-elim int
                            (lambda [p int] (= (+ p m) n))
                            (exists [p int] (= (+ p (pred m)) n)))
                 Hind <c3>))
      (have <d> _ :by (p/and-intro% <d1> <d2>)))
    "We apply integer induction."
    (have <e> (forall [m int]
                (exists [p int] (= (+ p m) n)))
          :by ((int/int-induct (lambda [m int] (exists [p int] (= (+ p m) n))))
               <a> <d>)))
  (qed <e>))


(deflemma minus-single
  [[n int] [m int]]
  (q/single int (lambda [p int]
                  (= (+ p m) n))))

(proof minus-single
    :script
  (assume [p1 int
           p2 int
           Hp1 (= (+ p1 m) n)
           Hp2 (= (+ p2 m) n)]
    (have <a> (= (+ p1 m) (+ p2 m))
          :by ((eq/eq-trans int (+ p1 m) n (+ p2 m))
               Hp1 (eq/eq-sym% Hp2)))
    (have <b> (= p1 p2)
          :by ((plus/plus-right-cancel p1 p2 m)
               <a>)))
  (have <c> (q/single int (lambda [p int] (= (+ p m) n)))
        :by <b>)
  (qed <c>))

(defthm minus-unique
  "The unicity property of subtraction."
  [[n int] [m int]]
  (q/unique int (lambda [p int]
                  (= (+ p m) n))))

(proof minus-unique
    :script
  (have <a> _ :by (p/and-intro% (minus-ex n m)
                                (minus-single n m)))
  (qed <a>))

(definition -
  "Integer subtraction."
  [[n int] [m int]]
  (q/the int (lambda [p int] (= (+ p m) n)) (minus-unique n m)))

(defthm minus-prop
  "The defining property of subtraction."
  [[n int] [m int]]
  (= (+ (- n m) m) n))

(proof minus-prop
    :term
  (q/the-prop int (lambda [p int] (= (+ p m) n)) (minus-unique n m)))


