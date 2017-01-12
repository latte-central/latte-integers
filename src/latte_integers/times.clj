(ns latte-integers.times
  "The multiplication defined on ℤ."

  (:refer-clojure :exclude [and or not int = + - *])

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
            [latte-integers.plus :as plus :refer [+]]
            [latte-integers.minus :as minus :refer [-]]))

(definition plus-fun
  "The addition function used in multiplication."
  [[m int]]
  (lambda [n int] (+ n m)))

(deflemma plus-fun-injective
  [[m int]]
  (fun/injective int int (plus-fun m)))

(proof plus-fun-injective
    :script
  (assume [n1 int
           n2 int
           Heq (= ((plus-fun m) n1) ((plus-fun m) n2))]
    (have <a> (= (+ n1 m) (+ n2 m)) :by Heq)
    (have <b> (= n1 n2)
          :by ((plus/plus-right-cancel n1 n2 m) <a>))
    (qed <b>)))

(deflemma plus-fun-surjective
  [[m int]]
  (fun/surjective int int (plus-fun m)))

(proof plus-fun-surjective
    :script
  (assume [n int]
    (have <a> (= ((plus-fun m) (- n m))
                 (+ (- n m) m))
          :by (eq/eq-refl int ((plus-fun m) (- n m))))
    (have <b> (= ((plus-fun m) (- n m))
                 n) :by (minus/minus-prop n m))
    (have <c> (q/ex int (lambda [x int] (= ((plus-fun m) x)
                                           n)))
          :by ((q/ex-intro int (lambda [x int] (= ((plus-fun m) x)
                                                  n)) (- n m))
               <b>))
    (qed <c>)))

(deflemma plus-fun-bijective
  [[m int]]
  (fun/bijective int int (plus-fun m)))

(proof plus-fun-bijective
    :script
  (have <a> _ :by (p/and-intro% (plus-fun-injective m)
                                (plus-fun-surjective m)))
  (qed <a>))

(definition mult-prop
  "The property of the multiplication function on integers."
  [[m int]]
  (lambda [g (==> int int)]
    (and (= (g zero) zero)
         (forall [x int]
           (= (g (succ x)) ((plus-fun m) (g x)))))))

(defthm mult-unique
  "The unicity of the multiplication function, through [[mult-prop]]."
  [[m int]]
  (q/unique (==> int int)
            (mult-prop m)))

(proof mult-unique
    :term
  (rec/int-recur-bijection int zero (plus-fun m) (plus-fun-bijective m)))

(definition times
  "The function that multiplies `m` to an integer"
  [[m int]]
  (q/the (==> int int)
         (mult-prop m)
         (mult-unique m)))

(definition *
  "The function that multiplies `m` with `n`."
  [[m int] [n int]]
  ((times m) n))

(defthm times-prop
  [[m int]]
  (and (= ((times m) zero) zero)
       (forall [n int]
         (= (* m (succ n))
            (+ (* m n) m)))))

(proof times-prop
    :term
  (q/the-prop
      (==> int int)
    (mult-prop m)
    (mult-unique m)))

(defthm times-zero
  [[n int]]
  (= (* n zero)
     zero))

(proof times-zero
    :script
  (have <a> _ :by (p/and-elim-left% (times-prop n)))
  (qed <a>))

(defthm times-succ
  [[m int] [n int]]
  (= (* m (succ n))
     (+ (* m n) m)))

(proof times-succ
    :script
  (have <a> _ :by ((p/and-elim-right% (times-prop m)) n))
  (qed <a>))


(defthm times-pred
  [[m int] [n int]]
  (= (* m (pred n))
     (- (* m n) m)))

(proof times-pred
    :script
  (have <a> (= (* m (succ (pred n)))
               (+ (* m (pred n)) m))
        :by (times-succ m (pred n)))

  ;; (- (+ (* m (pred n)) m) m) = (-)

  )
