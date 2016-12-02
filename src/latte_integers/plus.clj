
(ns latte-integers.plus
  "The addition defined on ℤ."

  (:refer-clojure :exclude [and or not int = +])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          try-proof ==>]]

            [latte.prop :as p :refer [and or not <=>]]
            [latte.equal :as eq :refer [equal]]
            [latte.quant :as q]
            [latte.fun :as fun]

            [latte-sets.core :as set :refer [elem forall-in]]

            [latte-integers.core :as int :refer [zero succ pred int =]]
            [latte-integers.nat :as nat :refer [positive negative]]
            [latte-integers.rec :as rec]))

(definition add-prop
  "The property of the addition function on integers."
  [[m int]]
  (lambda [g (==> int int)]
    (and (= (g zero) m)
         (forall [x int]
           (= (g (succ x)) (succ (g x)))))))

(defthm add-unique
  "The unicity of the addition function, through [[add-prop]]."
  [[m int]]
  (q/unique (==> int int)
            (add-prop m)))

(proof add-unique
    :term
  (rec/int-recur-bijection int m succ int/succ-bijective))

(definition plus
  "The function that adds `m` to an integer"
  [[m int]]
  (q/the (==> int int)
         (add-prop m)
         (add-unique m)))

(definition +
  "The function that adds `m` to `n`."
  [[m int] [n int]]
  ((plus m) n))

(defthm plus-prop
  [[m int]]
  (and (= ((plus m) zero) m)
       (forall [n int]
         (= ((plus m) (succ n))
            (succ ((plus m) n))))))

(proof plus-prop
    :term
  (q/the-prop
      (==> int int)
    (add-prop m)
    (add-unique m)))

(defthm plus-zero
  [[m int]]
  (= (+ m zero) m))

(proof plus-zero
    :script
  (have <a> _ :by (p/and-elim-left% (plus-prop m)))
  (qed <a>))

(defthm plus-succ
  [[m int] [n int]]
  (= (+ m (succ n))
     (succ (+ m n))))

(proof plus-succ
    :script
  (have <a> _ :by ((p/and-elim-right% (plus-prop m)) n))
  (qed <a>))


(defthm plus-pred
  [[m int] [n int]]
  (= (+ m (pred n))
     (pred (+ m n))))

(proof plus-pred
    :script
  (have <a> (= (+ m (succ (pred n)))
               (succ (+ m (pred n))))
        :by (plus-succ m (pred n)))
  (have <b> (= (+ m n)
               (succ (+ m (pred n))))
        :by ((eq/eq-subst
              int
              (lambda [k int]
                (= (+ m k)
                   (succ (+ m (pred n)))))
              (succ (pred n))
              n)
             (int/succ-of-pred n)
             <a>))
  (have <c> (= (pred (+ m n))
               (pred (succ (+ m (pred n)))))
        :by ((eq/eq-cong int int pred
                         (+ m n) (succ (+ m (pred n))))
             <b>))
  (have <d> (= (pred (+  m n))
               (+ m (pred n)))
        :by ((eq/eq-subst int
                          (lambda [k int]
                            (= (pred (+ m n)) k))
                          (pred (succ (+ m (pred n))))
                          (+ m (pred n)))
             (int/pred-of-succ (+ m (pred n)))
             <c>))
  (have <e> _ :by ((eq/eq-sym int
                              (pred (+ m n))
                              (+ m (pred n))) <d>))
  (qed <e>))


