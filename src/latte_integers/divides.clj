(ns latte-integers.divides
  
  "The divisibility relation defined on ℤ."
  
  (:refer-clojure :exclude [and or not int = + - *])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          pose try-proof ==>]]

            [latte.prop :as p :refer [and or not <=>]]
            [latte.equal :as eq :refer [equal]]
            [latte.quant :as q :refer [exists]]
            [latte.fun :as fun]

            [latte-sets.core :as set :refer [elem forall-in]]

            [latte-integers.core :as int :refer [zero one succ pred int =]]
            [latte-integers.nat :as nat :refer [nat positive negative]]
            [latte-integers.rec :as rec]
            [latte-integers.plus :as plus :refer [+]]
            [latte-integers.minus :as minus :refer [- --]]
            [latte-integers.times :as times :refer [*]]))

(definition divides
  "The divisibility relation.
`(divides m n)` says that `m` divides `n`."
  [[m int] [n int]]
  (exists [p int]
    (= (* m p) n)))

(defthm divides-zero
  [[n int]]
  (divides n zero))

(proof divides-zero
    :script

  (have <a> (= (* n zero) zero)
        :by (times/times-zero n))

  (have <b> (exists [p int]
              (= (* n p) zero))
        :by ((q/ex-intro int (lambda [p int]
                               (= (* n p) zero)) zero)
             <a>))
  (qed <b>))

(defthm divides-zero-zero
  []
  (divides zero zero))

(proof divides-zero-zero
    :term
  (divides-zero zero))

(defthm divides-zero-conv
  [[n int]]
  (==> (divides zero n)
       (= n zero)))

(proof divides-zero-conv
    :script
  (assume [Hn (divides zero n)]
    (assume [p int
             Hp (= (* zero p) n)]
      (have <a> (= (* zero p) zero)
            :by (times/times-zero-swap p))
      (have <b> (= zero n)
            :by (eq/eq-subst% (lambda [k int]
                                (= k n))
                              <a> Hp))
      (have <c> (= n zero) :by (eq/eq-sym% <b>)))
    (have <d> (= n zero)
          :by ((q/ex-elim int (lambda [p int]
                                (= (* zero p) n))
                          (= n zero))
               Hn <c>))
    (qed <d>)))

(defthm divides-opp
  [[m int] [n int]]
  (==> (divides m n)
       (divides (-- m) n)))


(proof divides-opp
    :script
  (assume [Hnm (divides m n)]
    (assume [p int
             Hp (= (* m p) n)]
      
      (have <a> (= (* m p) (* (-- m) (-- p)))
            :by (eq/eq-sym% (times/times-opp-opp m p)))
      (have <b> (= (* (-- m) (-- p)) n)
            :by (eq/eq-subst% (lambda [k int]
                                (= k n))
                              <a> Hp))
      (have <c> (divides (-- m) n)
            :by ((q/ex-intro int (lambda [k int]
                                   (= (* (-- m) k) n)) (-- p))
                 <b>)))
    (have <d> _ :by ((q/ex-elim int (lambda [k int]
                                      (= (* m k) n))
                                (divides (-- m) n))
                     Hnm <c>))
    (qed <d>)))

(defthm divides-one
  [[n int]]
  (divides one n))

(proof divides-one
    :script
  (have <a> (= (* one n) n)
        :by (times/times-one-swap n))
  (have <b> (divides one n)
        :by ((q/ex-intro int (lambda [p int]
                               (= (* one p) n)) n)
             <a>))
  (qed <b>))

(defthm divides-refl
  [[n int]]
  (divides n n))

(proof divides-refl
    :script
  (have <a> (= (* n one) n)
        :by (times/times-one n))
  (have <b> _
        :by ((q/ex-intro int (lambda [p int]
                               (= (* n p) n)) one)
             <a>))
  (qed <b>))

(defthm divides-trans
  [[m int] [n int] [p int]]
  (==> (divides m n)
       (divides n p)
       (divides m p)))

(proof divides-trans
    :script
  (assume [Hnm (divides m n)
           Hmp (divides n p)]
    (assume [a int
             Hp (= (* m a) n)]
      (assume [b int
               Hq (= (* n b) p)]
        (have <a> (= n (* m a)) :by (eq/eq-sym% Hp))
        (have <b> (= (* (* m a) b) p)
              :by (eq/eq-subst% (lambda [k int]
                                  (= (* k b) p))
                                <a>
                                Hq))
        (have <c> (= (* m (* a b)) p)
              :by (eq/eq-subst% (lambda [k int]
                                  (= k p))
                                (times/times-assoc m a b)
                                <b>))
        (have <d> (divides m p)
              :by ((q/ex-intro int (lambda [k int]
                                     (= (* m k) p)) (* a b))
                   <c>)))
      (have <e> (divides m p)
            :by ((q/ex-elim int (lambda [k int]
                                  (= (* n k) p))
                            (divides m p))
                 Hmp <d>)))
    (have <f> (divides m p)
          :by ((q/ex-elim int (lambda [k int]
                                (= (* m k) n))
                          (divides m p))
               Hnm <e>))
    (qed <f>)))


