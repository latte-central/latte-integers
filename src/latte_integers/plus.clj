
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
  (have <e> _ :by (eq/eq-sym% <d>))
  (qed <e>))

(defthm plus-zero-sym
  [[m int]]
  (= (+ zero m) m))

(proof plus-zero-sym
    :script
  "We proceed by induction on `m`."
  "First the case for m=0"
  (have <a> (= (+ zero zero) zero)
        :by (plus-zero zero))
  "Then the inductive case, we assume `(P m)` for some `m`."
  (assume [m int
           Hind (= (+ zero m) m)]
    "We must show `(P (pred m))`."
    (have <b1> (= (+ zero (pred m))
                  (pred (+ zero m)))
          :by (plus-pred zero m))
    (have <b> (= (+ zero (pred m))
                 (pred m))
          :by ((eq/eq-subst int
                            (lambda [k int]
                              (= (+ zero (pred m))
                                 (pred k)))
                            (+ zero m)
                            m)
               Hind <b1>))
    "and also  and `(P (succ m))`."
    (have <c1> (= (+ zero (succ m))
                  (succ (+ zero m)))
          :by (plus-succ zero m))
    (have <c> (= (+ zero (succ m))
                 (succ m))
          :by ((eq/eq-subst int
                            (lambda [k int]
                              (= (+ zero (succ m))
                                 (succ k)))
                            (+ zero m)
                            m)
               Hind <c1>))
    (have <d> _ :by (p/and-intro% <c> <b>)))
  (qed (((int/int-induct (lambda [m int]
                           (= (+ zero m) m)))
         <a> <d>) m)))

(defthm plus-succ-sym
  [[m int] [n int]]
  (= (+ (succ m) n)
     (succ (+ m n))))

(proof plus-succ-sym
    :script
  (have <a1> (= (+ (succ m) zero)
                (succ m))
        :by (plus-zero (succ m)))
  (have <a2> (= (succ m)
                (succ (+ m zero)))
        :by ((eq/eq-cong int int succ m (+ m zero))
             (eq/eq-sym% (plus-zero m))))
  (have <a> (= (+ (succ m) zero)
               (succ (+ m zero)))
        :by (eq/eq-trans% <a1> <a2>))
  (assume [n int
           Hind (= (+ (succ m) n)
                   (succ (+ m n)))]
    "We first show `(P (pred n))`."
    (have <b1> (= (+ (succ m) (pred n))
                  (pred (+ (succ m) n)))
          :by (plus-pred (succ m) n))
    (have <b2> (= (pred (+ (succ m) n))
                  (pred (succ (+ m n))))
          :by ((eq/eq-cong int int pred
                           (+ (succ m) n)
                           (succ (+ m n)))
               Hind))
    (have <b3> (= (+ (succ m) (pred n))
                  (pred (succ (+ m n))))
          :by (eq/eq-trans% <b1> <b2>))
    (have <b4> (= (+ (succ m) (pred n))
                  (+ m n))
          :by ((eq/eq-subst int
                            (lambda [k int]
                              (= (+ (succ m) (pred n))
                                 k))
                            (pred (succ (+ m n)))
                            (+ m n))
               (int/pred-of-succ (+ m n))
               <b3>))
    (have <b5> (= (+ m (succ (pred n)))
                  (succ (+ m (pred n))))
          :by (plus-succ m (pred n)))
    (have <b6> (= (+ m n)
                  (+ m (succ (pred n))))
          :by ((eq/eq-subst int
                            (lambda [k int]
                              (= (+ m n)
                                 (+ m k)))
                            n
                            (succ (pred n)))
               (eq/eq-sym% (int/succ-of-pred n))
               (eq/eq-refl int (+ m n))))
    (have <b7> (= (+ m n)
                  (succ (+ m (pred n))))
          :by (eq/eq-trans% <b6> <b5>))
    (have <b> (= (+ (succ m) (pred n))
                 (succ (+ m (pred n))))
          :by (eq/eq-trans% <b4> <b7>))
    "And then `P (succ n)`."
    (have <c1> (= (+ (succ m) (succ n))
                  (succ (+ (succ m) n)))
          :by (plus-succ (succ m) n))
    (have <c2> (= (succ (+ (succ m) n))
                  (succ (succ (+ m n))))
          :by ((eq/eq-cong int int succ
                           (+ (succ m) n)
                           (succ (+ m n))) Hind))
    (have <c3> (= (+ (succ m) (succ n))
                  (succ (succ (+ m n))))
          :by (eq/eq-trans% <c1> <c2>))
    (have <c4> (= (succ (succ (+ m n)))
                  (succ (+ m (succ n))))
          :by ((eq/eq-cong int int succ
                           (succ (+ m n))
                           (+ m (succ n)))
               (eq/eq-sym% (plus-succ m n))))
    (have <c> (= (+ (succ m) (succ n))
                 (succ (+ m (succ n))))
          :by (eq/eq-trans% <c3> <c4>))
    "Let's conjunct the two sides."
    (have <d> _ :by (p/and-intro% <c> <b>)))
  (qed (((int/int-induct (lambda [n int]
                           (= (+ (succ m) n)
                              (succ (+ m n)))))
         <a> <d>) n)))

(defthm plus-pred-sym
  [[m int] [n int]]
  (= (+ (pred m) n)
     (pred (+ m n))))

(proof plus-pred-sym
    :script
  (have <a> (= (+ (succ (pred m)) n)
               (succ (+ (pred m) n)))
        :by (plus-succ-sym (pred m) n))
  (have <b> (= (+ m n)
               (succ (+ (pred m) n)))
        :by ((eq/eq-subst int
                          (lambda [k int]
                            (= (+ k n)
                               (succ (+ (pred m) n))))
                          (succ (pred m))
                          m)
             (int/succ-of-pred m)
             <a>))
  (have <c> (= (pred (+ m n))
               (pred (succ (+ (pred m) n))))
        :by ((eq/eq-cong int int pred
                         (+ m n)
                         (succ (+ (pred m) n)))
             <b>))
  (have <d> (= (pred (+ m n))
               (+ (pred m) n))
        :by ((eq/eq-subst int
                          (lambda [k int]
                            (= (pred (+ m n))
                               k))
                          (pred (succ (+ (pred m) n)))
                          (+ (pred m) n))
             (int/pred-of-succ (+ (pred m) n))
             <c>))
  (qed ((eq/eq-sym int (pred (+ m n))
                   (+ (pred m) n)) <d>)))

