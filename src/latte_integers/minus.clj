
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

(defthm minus-prop-cons
  "A consequence of [[minus-prop]]."
  [[n int] [m int]]
  (= (- (+ n m) m) n))

(proof minus-prop-cons
    :script
  (have <a> (= (+ (- (+ n m) m) m)
               (+ n m))
        :by (minus-prop (+ n m) m))
  (have <b> (= (- (+ n m) m) n)
        :by ((plus/plus-right-cancel (- (+ n m) m)
                                     n
                                     m)
             <a>))
  (qed <b>))

(defthm minus-cancel
  [[n int]]
  (= (- n n) zero))

(proof minus-cancel
    :script
  (have <a> (= (+ (- n n) n) n)
        :by (minus-prop n n))
  (have <b> (= n (+ zero n))
        :by (eq/eq-sym% (plus/plus-zero-sym n)))
  (have <c> (= (+ (- n n) n)
               (+ zero n))
        :by (eq/eq-trans% <a> <b>))
  (have <d> (= (- n n) zero)
        :by ((plus/plus-right-cancel (- n n) zero n)
             <c>))
  (qed <d>))

(defthm minus-zero
  [[n int]]
  (= (- n zero) n))

(proof minus-zero
    :script
  (have <a> (= (- (+ n zero) zero) n)
        :by (minus-prop-cons n zero))
  (have <b> (= (- n zero) n)
        :by (eq/eq-subst% (lambda [k int] (= (- k zero) n))
                          (plus/plus-zero n)
                          <a>))
  (qed <b>))

(defthm minus-succ-pred
  [[n int] [m int]]
  (= (- n (succ m))
     (pred (- n m))))

(proof minus-succ-pred
    :script
  (have <a> (= (+ (- n (succ m)) (succ m))
               n)
        :by (minus-prop n (succ m)))
  (have <b> (= (+ (pred (- n m)) (succ m))
               (+ (- n m) m))
        :by (plus/plus-pred-succ (- n m) m))
  (have <c> (= (+ (- n m) m)
               n)
        :by (minus-prop n m))
  (have <d> (= (+ (pred (- n m)) (succ m))
               n)
        :by (eq/eq-trans% <b> <c>))
  (have <e> (= n
               (+ (pred (- n m)) (succ m))) :by (eq/eq-sym% <d>))
  (have <f> (= (+ (- n (succ m)) (succ m))
               (+ (pred (- n m)) (succ m)))
        :by (eq/eq-trans% <a> <e>))
  (have <g> (= (- n (succ m))
               (pred (- n m)))
        :by ((plus/plus-right-cancel (- n (succ m))
                                     (pred (- n m))
                                     (succ m)) <f>))
  (qed <g>))

(defthm minus-pred-succ
  [[n int] [m int]]
  (= (- n (pred m))
     (succ (- n m))))

(proof minus-pred-succ
    :script
  (have <a> (= (+ (- n (pred m)) (pred m))
               n)
        :by (minus-prop n (pred m)))
  (have <b> (= (+ (succ (- n m)) (pred m))
               (+ (- n m) m))
        :by (plus/plus-succ-pred (- n m) m))
  (have <c> (= (+ (- n m) m)
               n)
        :by (minus-prop n m))
  (have <d> (= (+ (succ (- n m)) (pred m))
               n)
        :by (eq/eq-trans% <b> <c>))
  (have <e> (= n
               (+ (succ (- n m)) (pred m)))
        :by (eq/eq-sym% <d>))
  (have <f> (= (+ (- n (pred m)) (pred m))
               (+ (succ (- n m)) (pred m)))
        :by (eq/eq-trans% <a> <e>))
  (have <g> (= (- n (pred m))
               (succ (- n m)))
        :by ((plus/plus-right-cancel (- n (pred m))
                                     (succ (- n m))
                                     (pred m)) <f>))
  (qed <g>))

(defthm minus-succ
  [[n int] [m int]]
  (= (- (succ n) m)
     (succ (- n m))))


(proof minus-succ
    :script
  (have <a> (= (+ (- (succ n) m) m)
               (succ n))
        :by (minus-prop (succ n) m))

  ;; (succ (+ (- n m) m))
  ;; = (succ n)
  (have <b> (= (succ (+ (- n m) m))
               (succ n))
        :by (eq/eq-cong% succ (minus-prop n m)))

  (have <c> (= (+ (succ (- n m)) m)
               (succ (+ (- n m) m)))
        :by (plus/plus-succ-sym (- n m) m))
  
  (have <e> (= (+ (succ (- n m)) m)
               (succ n))
        :by (eq/eq-trans% <c> <b>))

  (have <f> (= (succ n)
               (+ (succ (- n m)) m))
        :by (eq/eq-sym% <e>))

  (have <g> (= (+ (- (succ n) m) m)
               (+ (succ (- n m)) m))
        :by (eq/eq-trans% <a> <f>))
  (have <h> (= (- (succ n) m)
               (succ (- n m)))
        :by ((plus/plus-right-cancel (- (succ n) m)
                                     (succ (- n m))
                                     m) <g>))
  (qed <h>))

(definition opp
  "The opposite of an integer."
  [[n int]]
  (- zero n))


