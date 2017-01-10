
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
  (have <b> (= (succ (+ (- n m) m))
               (succ n))
        :by (eq/eq-cong% succ (minus-prop n m)))

  (have <c> (= (+ (succ (- n m)) m)
               (succ (+ (- n m) m)))
        :by (plus/plus-succ-sym (- n m) m))
  (have <d> (= (+ (succ (- n m)) m)
               (succ n))
        :by (eq/eq-trans% <c> <b>))
  (have <e> (= (succ n)
               (+ (succ (- n m)) m))
        :by (eq/eq-sym% <d>))
  (have <f> (= (+ (- (succ n) m) m)
               (+ (succ (- n m)) m))
        :by (eq/eq-trans% <a> <e>))
  (have <g> (= (- (succ n) m)
               (succ (- n m)))
        :by ((plus/plus-right-cancel (- (succ n) m)
                                     (succ (- n m))
                                     m) <f>))
  (qed <g>))

(defthm minus-pred
  [[n int] [m int]]
  (= (- (pred n) m)
     (pred (- n m))))

(proof minus-pred
    :script
  (have <a> (= (+ (- (pred n) m) m)
               (pred n))
        :by (minus-prop (pred n) m))
  (have <b> (= (pred (+ (- n m) m))
               (pred n))
        :by (eq/eq-cong% pred (minus-prop n m)))
  (have <c> (= (+ (pred (- n m)) m)
               (pred (+ (- n m) m)))
        :by (plus/plus-pred-sym (- n m) m))
  (have <d> (= (+ (pred (- n m)) m)
               (pred n))
        :by (eq/eq-trans% <c> <b>))
  (have <e> (= (pred n)
               (+ (pred (- n m)) m))
        :by (eq/eq-sym% <d>))
  (have <f> (= (+ (- (pred n) m) m)
               (+ (pred (- n m)) m))
        :by (eq/eq-trans% <a> <e>))
  (have <g> (= (- (pred n) m)
               (pred (- n m)))
        :by ((plus/plus-right-cancel (- (pred n) m)
                                     (pred (- n m))
                                     m) <f>))
  (qed <g>))


(defthm minus-one
  [[n int]]
  (= (- n (succ zero)) (pred n)))

(proof minus-one
    :script
  (have <a> (= (- n (succ zero))
               (pred (- n zero)))
        :by (minus-succ-pred n zero))
  (have <b> (= (pred (- n zero))
               (pred n))
        :by (eq/eq-cong% pred (minus-zero n)))
  (have <c> (= (- n (succ zero))
               (pred n))
        :by (eq/eq-trans% <a> <b>))
  (qed <c>))

(defthm minus-right-cancel
  [[n int] [m int] [p int]]
  (==> (= (- n p) (- m p))
       (= n m)))

(proof minus-right-cancel
    :script
  (assume [H (= (- n p) (- m p))]
    (have <a> (= (+ (- n p) p)
                 (+ (- m p) p))
          :by (eq/eq-cong% (lambda [k int] (+ k p))
                           H))
    (have <b> (= (+ (- n p) p) n)
          :by (minus-prop n p))
    (have <c> (= (+ (- m p) p) m)
          :by (minus-prop m p))
    (have <d> (= n (+ (- m p) p))
          :by (eq/eq-subst% (lambda [k int] (= k (+ (- m p) p)))
                            <b> <a>))
    (have <e> (= n m)
          :by (eq/eq-subst% (lambda [k int] (= n k))
                            <c> <d>))
    (qed <e>)))

(defthm minus-left-cancel
  [[n int] [m int] [p int]]
  (==> (= (- n m) (- n p))
       (= m p)))

(proof minus-left-cancel
    :script
  (assume [H (= (- n m) (- n p))]
    (have <a> (= (+ (- n m) m)
                 (+ (- n p) m))
          :by (eq/eq-cong% (lambda [k int] (+ k m)) H))
    (have <b> (= n (+ (- n p) m))
          :by (eq/eq-subst% (lambda [k int] (= k (+ (- n p) m)))
                            (minus-prop n m)
                            <a>))
    (have <c> (= (+ (- n m) p)
                 (+ (- n p) p))
          :by (eq/eq-cong% (lambda [k int] (+ k p)) H))
    (have <d> (= (+ (- n m) p) n)
          :by (eq/eq-subst% (lambda [k int] (= (+ (- n m) p) k))
                            (minus-prop n p)
                            <c>))
    (have <e> (= (+ (- n m) p)
                 (+ (- n p) m))
          :by (eq/eq-trans% <d> <b>))

    (have <f> (= (+ (- n p) p)
                 (+ (- n p) m))
          :by (eq/eq-subst% (lambda [k int] (= (+ k p)
                                               (+ (- n p) m)))
                            H <e>))
    (have <g> (= p m)
          :by ((plus/plus-left-cancel p m (- n p)) <f>))
    (have <h> (= m p) :by (eq/eq-sym% <g>))
    (qed <h>)))

(defthm assoc-plus-minus
  [[n int] [m int] [p int]]
  (= (+ n (- m p))
     (- (+ n m) p)))

(proof assoc-plus-minus
    :script
  (have <a> (= (+ (+ n (- m p)) p)
               (+ n (+ (- m p) p)))
        :by (eq/eq-sym% (plus/plus-assoc n (- m p) p)))
  (have <b> (= (+ n (+ (- m p) p))
               (+ n m))
        :by (eq/eq-cong% (lambda [k int] (+ n k))
                         (minus-prop m p)))
  (have <c> (= (+ (+ n (- m p)) p)
               (+ n m))
        :by (eq/eq-trans% <a> <b>))
  (have <d> (= (+ (- (+ n m) p) p)
               (+ n m)) :by (minus-prop (+ n m) p))
  (have <e> (= (+ n m)
               (+ (- (+ n m) p) p))
        :by (eq/eq-sym% <d>))
  (have <f> (= (+ (+ n (- m p)) p)
               (+ (- (+ n m) p) p))
        :by (eq/eq-trans% <c> <e>))
  (have <g> (= (+ n (- m p))
               (- (+ n m) p))
        :by ((plus/plus-right-cancel (+ n (- m p))
                                     (- (+ n m) p)
                                     p) <f>))
  (qed <g>))

(defthm assoc-minus-plus
  [[n int] [m int] [p int]]
  (= (- n (+ m p))
     (- (- n m) p)))

(proof assoc-minus-plus
    :script

  (have <a> (= (+ (- n (+ m p)) (+ m p))
               n)
        :by (minus-prop n (+ m p)))

  (have <b> (= (+ (- (- n m) p) (+ m p))
               (+ (+ m p) (- (- n m) p)))
        :by (plus/plus-commute (- (- n m) p)
                               (+ m p)))

  (have <c1> (= (+ (+ m p) (- (- n m) p))
                (- (+ (+ m p) (- n m)) p))
        :by (assoc-plus-minus (+ m p) (- n m) p))

  (have <c> (= (+ (- (- n m) p) (+ m p))
               (- (+ (+ m p) (- n m)) p))
        :by (eq/eq-trans% <b> <c1>))

  (have <d1> (= (- (+ (+ m p) (- n m)) p)
                (- (- (+ (+ m p) n) m) p))
        :by (eq/eq-cong% (lambda [k int] (- k p))
                         (assoc-plus-minus (+ m p) n m)))

  (have <d> (= (+ (- (- n m) p) (+ m p))
               (- (- (+ (+ m p) n) m) p))
        :by (eq/eq-trans% <c> <d1>))

  (have <e1> (= (- (+ (+ m p) n) m)
                (- (+ (+ p m) n) m))
        :by (eq/eq-cong% (lambda [k int] (- (+ k n) m))
                         (plus/plus-commute m p)))
  
  (have <e2> (= (- (+ (+ p m) n) m)
                (- (+ p (+ m n)) m))
        :by (eq/eq-cong% (lambda [k int] (- k m))
                         (plus/plus-assoc-sym p m n)))

  (have <e3> (= (- (+ (+ m p) n) m)
                (- (+ p (+ m n)) m))
        :by (eq/eq-trans% <e1> <e2>))
  
  (have <e4> (= (- (+ p (+ m n)) m)
                (- (+ p (+ n m)) m))
        :by (eq/eq-cong% (lambda [k int] (- (+ p k) m))
                         (plus/plus-commute m n)))

  (have <e5> (= (- (+ (+ m p) n) m)
                (- (+ p (+ n m)) m))
        :by (eq/eq-trans% <e3> <e4>))
  
  
  (have <e6> (= (- (+ p (+ n m)) m)
                (- (+ (+ p n) m) m))
        :by (eq/eq-cong% (lambda [k int] (- k m))
                         (plus/plus-assoc p n m)))

  (have <e7> (= (- (+ (+ m p) n) m)
                (- (+ (+ p n) m) m))
        :by (eq/eq-trans% <e5> <e6>))
  
  (have <e8> (= (- (+ (+ p n) m) m)
                (+ p n))
        :by (minus-prop-cons (+ p n) m))

  (have <e9> (= (- (+ (+ m p) n) m)
                (+ p n))
        :by (eq/eq-trans% <e7> <e8>))
 
  ;; hence (- (- (+ (+ p m) n) m) p)
  ;;      = (- (+ p n) p)

  (have <e10> (= (- (- (+ (+ m p) n) m) p)
                 (- (+ p n) p))
        :by (eq/eq-cong% (lambda [k int] (- k p))
                         <e9>))

  ;;      = (- (+ n p) p)   by plus-commute

  (have <e11> (= (- (+ p n) p)
               (- (+ n p) p))
        :by (eq/eq-cong% (lambda [k int] (- k p))
                         (plus/plus-commute p n)))

  (have <e12> (= (- (+ n p) p)
                 n) :by (minus-prop-cons n p))

  (have <e13> (= (- (+ p n) p)
                 n) :by (eq/eq-trans% <e11> <e12>))

  (have <e> (= (- (- (+ (+ m p) n) m) p)
               n)
        :by (eq/eq-subst% (lambda [k int] (= (- (- (+ (+ m p) n) m) p)
                                             k))
                          <e13> <e10>))

  (have <f1> (= (+ (- (- n m) p) (+ m p))
                n)
        :by (eq/eq-trans% <d> <e>))

  (have <f> (= n (+ (- (- n m) p) (+ m p)))
        :by (eq/eq-sym% <f1>))
  

  (have <g> (= (+ (- n (+ m p)) (+ m p))
               (+ (- (- n m) p) (+ m p)))
        :by (eq/eq-trans% <a> <f>))

  (have <h> (= (- n (+ m p))
               (- (- n m) p))
        :by ((plus/plus-right-cancel (- n (+ m p))
                                     (- (- n m) p)
                                     (+ m p))
             <g>))

  (qed <h>))

(defthm assoc-minus-minus
  [[n int] [m int] [p int]]
  (= (- n (- m p))
     (+ (- n m) p)))

(proof assoc-minus-minus
    :script
  (have <a> (= (+ (- n (- m p)) (- m p))
               n) :by (minus-prop n (- m p)))
  (have <b> (= (+ (+ (- n m) p) (- m p))
               (+ (- m p) (+ (- n m) p)))
        :by (plus/plus-commute (+ (- n m) p) (- m p)))
  (have <c1> (= (+ (- m p) (+ (- n m) p))
                (+ (+ (- m p) (- n m)) p))
        :by (plus/plus-assoc (- m p) (- n m) p))
  (have <c> (= (+ (+ (- n m) p) (- m p))
               (+ (+ (- m p) (- n m)) p))
        :by (eq/eq-trans% <b> <c1>))

  (have <d1> (= (+ (- m p) (- n m))
                (+ (- n m) (- m p)))
        :by (plus/plus-commute (- m p) (- n m)))
  (have <d2> (= (+ (- n m) (- m p))
                (- (+ (- n m) m) p))
        :by (assoc-plus-minus (- n m) m p))
  (have <d3> (= (+ (- m p) (- n m))
                (- (+ (- n m) m) p))
        :by (eq/eq-trans% <d1> <d2>))
  (have <d> (= (+ (- m p) (- n m))
               (- n p))
        :by (eq/eq-subst% (lambda [k int] (= (+ (- m p) (- n m))
                                             (- k p)))
                          (minus-prop n m)
                          <d3>))

  (have <e1> (= (+ (+ (- n m) p) (- m p))
                (+ (- n p) p))
        :by (eq/eq-subst% (lambda [k int] (= (+ (+ (- n m) p) (- m p))
                                             (+ k p)))
                          <d>
                          <c>))

  (have <e2> (= (+ (+ (- n m) p) (- m p))
               n)
        :by (eq/eq-subst% (lambda [k int] (= (+ (+ (- n m) p) (- m p))
                                             k))
                          (minus-prop n p)
                          <e1>))
  (have <e> (= n (+ (+ (- n m) p) (- m p)))
        :by (eq/eq-sym% <e2>))

  (have <f> (= (+ (- n (- m p)) (- m p))
               (+ (+ (- n m) p) (- m p)))
        :by (eq/eq-trans% <a> <e>))

  (have <g> (= (- n (- m p))
               (+ (- n m) p))
        :by ((plus/plus-right-cancel (- n (- m p))
                                     (+ (- n m) p)
                                     (- m p)) <f>))
  (qed <g>))

(defthm minus-pos-neg
  [[n int] [m int]]
  (==> (positive (- n m))
       (negative (- m n))))


(proof minus-pos-neg
    :script
  (assume [Hpos (positive (- n m))]
    (assume [Hnat (elem int (- m n) nat)]
      (have <a> (elem int (+ (pred (- n m)) (- m n)) nat)
            :by (plus/plus-nat-closed (pred (- n m)) Hpos
                                      (- m n) Hnat))
      (have <b1> (= (+ (pred (- n m)) (- m n))
                    (pred (+ (- n m) (- m n))))
            :by (plus/plus-pred-sym (- n m) (- m n)))

      (have <b2> (= (pred (+ (- n m) (- m n)))
                    (pred (- (+ (- n m) m) n)))
            :by (eq/eq-cong% pred
                             (assoc-plus-minus (- n m) m n)))
      (have <b3> (= (+ (pred (- n m)) (- m n))
                    (pred (- (+ (- n m) m) n)))
            :by (eq/eq-trans% <b1> <b2>))

      (have <b4> (= (pred (- (+ (- n m) m) n))
                    (pred (- n n)))
            :by (eq/eq-cong% (lambda [k int] (pred (- k n)))
                             (minus-prop n m)))

      (have <b5> (= (+ (pred (- n m)) (- m n))
                    (pred (- n n)))
            :by (eq/eq-trans% <b3> <b4>))

      (have <b6> (= (+ (pred (- n m)) (- m n))
                    (pred zero))
            :by (eq/eq-subst% (lambda [k int] (= (+ (pred (- n m)) (- m n))
                                                 (pred k)))
                              (minus-cancel n)
                              <b5>))

      (have <b> (elem int (pred zero) nat)
            :by (eq/eq-subst% (lambda [k int] (elem int k nat))
                              <b6>
                              <a>))

      (have <c> p/absurd :by (nat/negative-pred-zero <b>)))
    (qed <c>)))

(defthm plus-zero-minus
  [[n int] [m int]]
  (= (+ (- zero n) m)
     (- m n)))

(proof plus-zero-minus
    :script
  (have <a> (= (+ (- zero n) m)
               (+ m (- zero n)))
        :by (plus/plus-commute (- zero n) m))
  (have <b> (= (+ m (- zero n))
               (- (+ m zero) n)) :by (assoc-plus-minus m zero n))
  (have <c> (= (+ (- zero n) m)
               (- (+ m zero) n)) :by (eq/eq-trans% <a> <b>))
  (have <d> (= (- (+ m zero) n)
               (- m n))
        :by (eq/eq-cong% (lambda [k int] (- k n))
                         (plus/plus-zero m)))
  (have <e> (= (+ (- zero n) m)
               (- m n)) :by (eq/eq-trans% <c> <d>))
  (qed <e>))

(defthm minus-pos-neg-conv
  [[n int] [m int]]
  (==> (negative (- m n))
       (positive (- n m))))

(proof minus-pos-neg-conv
    :script
  (assume [Hneg (negative (- m n))]
    (have <a> (exists [p int]
                (and (positive p) (= (+ (- m n) p) zero)))
          :by ((plus/negative-pos-plus (- m n))
               Hneg))
    (assume [p int
             Hp (and (positive p)
                     (= (+ (- m n) p) zero))]
      (have <b> (positive p) :by (p/and-elim-left% Hp))
      (have <c> (= (+ (- m n) p) zero) :by (p/and-elim-right% Hp))

      (have <d> (= (+ p (- m n)) zero)
            :by (eq/eq-subst% (lambda [k int] (= k zero))
                              (plus/plus-commute (- m n) p)
                              <c>))
      (have <e> (= (- (+ p (- m n)) (- m n))
                   (- zero (- m n)))
            :by (eq/eq-cong% (lambda [k int] (- k (- m n)))
                             <d>))

      (have <f> (= p (- zero (- m n)))
            :by (eq/eq-subst% (lambda [k int] (= k (- zero (- m n))))
                              (minus-prop-cons p (- m n))
                              <e>))

      (have <g> (= p (+ (- zero m) n))
            :by (eq/eq-subst% (lambda [k int] (= p k))
                              (assoc-minus-minus zero m n)
                              <f>))
      (have <h> (= p (- n m))
            :by (eq/eq-subst% (lambda [k int] (= p k))
                              (plus-zero-minus m n)
                              <g>))
      (have <i> (positive (- n m))
            :by (eq/eq-subst% (lambda [k int] (positive k))
                              <h>
                              <b>)))
    (have <j> (positive (- n m))
          :by ((q/ex-elim int (lambda [k int]
                                (and (positive k) (= (+ (- m n) k) zero)))
                          (positive (- n m)))
               <a> <i>))
    (qed <j>)))

(defthm minus-pos-neg-equiv
  [[n int] [m int]]
  (<=> (positive (- n m))
       (negative (- m n))))

(proof minus-pos-neg-equiv
    :script
  (have <a> _
        :by (p/and-intro% (minus-pos-neg n m) (minus-pos-neg-conv n m)))

  (qed <a>))


(definition --
  "The opposite of an integer."
  [[n int]]
  (- zero n))

(defthm opp-plus-opp
  [[n int]]
  (= (+ (-- n) n)
     zero))

(proof opp-plus-opp
    :script

  (have <a> (= (+ (-- n) n)
               (+ n (- zero n)))
        :by (plus/plus-commute (-- n) n))

  (have <b1> (= (+ n (- zero n))
                (- (+ n zero) n))
        :by (assoc-plus-minus n zero n))

  (have <b> (= (+ (-- n) n)
               (- (+ n zero) n))
        :by (eq/eq-trans% <a> <b1>))

  (have <c1> (= (- (+ n zero) n)
                (- n n))
        :by (eq/eq-cong% (lambda [k int] (- k n))
                         (plus/plus-zero n)))

  (have <c> (= (+ (-- n) n)
               (- n n))
        :by (eq/eq-trans% <b> <c1>))

  (have <d> (= (+ (-- n) n)
               zero)
        :by (eq/eq-subst% (lambda [k int] (= (+ (-- n) n)
                                             k))
                          (minus-cancel n)
                          <c>))
  (qed <d>))

(defthm plus-opp-minus
  [[n int] [m int]]
  (= (+ n (-- m))
     (- n m)))

(proof plus-opp-minus
    :script
  (have <a> (= (+ n (- zero m))
               (- (+ n zero) m))
        :by (assoc-plus-minus n zero m))

  (have <b> (= (+ n (-- m))
               (- n m))
        :by (eq/eq-subst% (lambda [k int] (= (+ n (-- m))
                                             (- k m)))
                          (plus/plus-zero n)
                          <a>))
  (qed <b>))

(defthm opp-plus
  [[n int] [m int]]
  (= (-- (+ n m))
     (- (-- n) m)))

(proof opp-plus
    :script
  (have <a> (= (- zero (+ n m))
               (- (- zero n) m))
        :by (assoc-minus-plus zero n m))
  (qed <a>))


(defthm opp-zero
  []
  (= (-- zero) zero))

(proof opp-zero
    :script
  (have <a> (= (- zero zero)
               zero)
        :by (minus-zero zero))
  (qed <a>))

(defthm opp-opp
  [[n int]]
  (= (-- (-- n))
     n))

(proof opp-opp
    :script
  (have <a> (= (- zero (- zero n))
               (+ (- zero zero) n))
        :by (assoc-minus-minus zero zero n))
  (have <b> (= (-- (-- n))
               (+ zero n))
        :by (eq/eq-subst% (lambda [k int] (= (-- (-- n))
                                             (+ k n)))
                          (minus-zero zero)
                          <a>))
  (have <c> (= (-- (-- n))
               n)
        :by (eq/eq-subst% (lambda [k int] (= (-- (-- n))
                                             k))
                          (plus/plus-zero-sym n)
                          <b>))
  (qed <c>))


(defthm zero-opp-zero
  [[n int]]
  (==> (= n zero)
       (= (-- n) zero)))

(proof zero-opp-zero
    :script
  (assume [H (= n zero)]
    (have <a> (= (-- n) (-- zero))
          :by (eq/eq-cong% (lambda [k int] (-- k))
                           H))
    (have <b> (= (-- n) zero)
          :by (eq/eq-subst% (lambda [k int] (= (-- n) k))
                            (opp-zero)
                            <a>)))
  (qed <b>))

(defthm zero-opp-zero-conv
  [[n int]]
  (==> (= (-- n) zero)
       (= n zero)))

(proof zero-opp-zero-conv
    :script
  (assume [H (= (-- n) zero)]
    (have <a> (= (+ (-- n) n)
                 (+ zero n))
          :by ((plus/plus-right-cancel-conv (-- n) zero n)
               H))
    (have <b> (= zero
                 (+ zero n))
          :by (eq/eq-subst% (lambda [k int] (= k (+ zero n)))
                            (opp-plus-opp n)
                            <a>))

    (have <c> (= zero n)
          :by (eq/eq-subst% (lambda [k int] (= zero k))
                            (plus/plus-zero-sym n)
                            <b>))

    (have <d> (= n zero) :by (eq/eq-sym% <c>)))
  (qed <d>))


(defthm zero-opp-zero-equiv
  [[n int]]
  (<=> (= n zero)
       (= (-- n) zero)))

(proof zero-opp-zero-equiv
    :script
  (have <a> _ :by (p/and-intro% (zero-opp-zero n)
                                (zero-opp-zero-conv n)))
  (qed <a>))


(defthm opp-succ-pred
  [[n int]]
  (= (-- (succ n))
     (pred (-- n))))

(proof opp-succ-pred
    :script
  (have <a> (= (- zero (succ n))
               (pred (- zero n)))
        :by (minus-succ-pred zero n))
  (qed <a>))

(defthm opp-pred-succ
  [[n int]]
  (= (-- (pred n))
     (succ (-- n))))

(proof opp-pred-succ
    :script
  (have <a> (= (- zero (pred n))
               (succ (- zero n)))
        :by (minus-pred-succ zero n))
  (qed <a>))

(defthm opp-pos-neg
  [[n int]]
  (==> (positive n)
       (negative (-- n))))

(proof opp-pos-neg
    :script
  (assume [H (positive n)]
    (have <a> (positive (- n zero))
          :by ((eq/eq-subst int
                            (lambda [k int] (positive k))
                            n (- n zero))
               ((eq/eq-sym int (- n zero) n)
                (minus-zero n))
               H))
    (have <b> (negative (- zero n))
          :by ((minus-pos-neg n zero) <a>)))
  (qed <b>))

(defthm opp-pos-neg-conv
  [[n int]]
  (==> (negative (-- n))
       (positive n)))

(proof opp-pos-neg-conv
    :script
  (assume [H (negative (-- n))]
    (have <a> (positive (- n zero))
          :by ((minus-pos-neg-conv n zero) H))
    (have <b> (positive n)
          :by (eq/eq-subst% positive
                            (minus-zero n)
                            <a>)))
  (qed <b>))

(defthm opp-pos-neg-equiv
  [[n int]]
  (<=> (positive n)
       (negative (-- n))))

(proof opp-pos-neg-equiv
    :script
  (have <a> _ :by (p/and-intro% (opp-pos-neg n)
                                (opp-pos-neg-conv n)))
  (qed <a>))


(defthm opp-neg-pos
  [[n int]]
  (==> (negative n)
       (positive (-- n))))

(proof opp-neg-pos
    :script
  (assume [H (negative n)]
    (have <a> (negative (-- (-- n)))
          :by ((eq/eq-subst int negative
                           n (-- (-- n)))
               (eq/eq-sym% (opp-opp n))
               H))
    (have <b> (positive (-- n))
          :by ((opp-pos-neg-conv (-- n)) <a>)))
  (qed <b>))

(defthm opp-neg-pos-conv
  [[n int]]
  (==> (positive (-- n))
       (negative n)))

(proof opp-neg-pos-conv
    :script
  (assume [H (positive (-- n))]
    (have <a> (negative (-- (-- n)))
          :by ((opp-pos-neg (-- n)) H))
    (have <b> (negative n)
          :by (eq/eq-subst% negative
                            (opp-opp n)
                            <a>)))
  (qed <b>))

(defthm opp-neg-pos-equiv
  [[n int]]
  (<=> (negative n)
       (positive (-- n))))

(proof opp-neg-pos-equiv
    :script
  (have <a> _ :by (p/and-intro% (opp-neg-pos n)
                                (opp-neg-pos-conv n)))
  (qed <a>))

(defthm opp-pos-split
  "A split for integers using the opposite, using [[nat/positive]]."
  [[n int]]
  (or (or (= n zero)
          (positive n))
      (positive (-- n))))

(proof opp-pos-split
    :script
  (assume [H1 (or (= n zero)
                  (positive n))]
    (have <a> (or (or (= n zero)
                      (positive n))
                  (positive (-- n)))
          :by (p/or-intro-left% H1
                                (positive (-- n)))))
  (assume [H2 (negative n)]
    (have <b1> (positive (-- n))
          :by ((opp-neg-pos n) H2))
    (have <b> (or (or (= n zero)
                      (positive n))
                  (positive (-- n)))
          :by (p/or-intro-right% (or (= n zero)
                                     (positive n))
                                 <b1>)))
  (have <c> _ :by (p/or-elim% (nat/int-split n)
                              (or (or (= n zero)
                                      (positive n))
                                  (positive (-- n)))
                              <a> <b>))
  (qed <c>))

(defthm opp-neg-split
  "A split for integers using the opposite, using [[nat/negative]]."
  [[n int]]
  (or (or (= n zero)
          (negative n))
      (negative (-- n))))

(proof opp-neg-split
    :script
  (assume [H1 (or (= n zero)
                  (positive n))]
    (assume [H2 (= n zero)]
      (have <a1> (or (= n zero)
                     (negative n))
            :by (p/or-intro-left% H2 (negative n)))
      (have <a> (or (or (= n zero)
                        (negative n))
                    (negative (-- n)))
            :by (p/or-intro-left% <a1> (negative (-- n)))))
    (assume [H3 (positive n)]
      (have <b> (or (or (= n zero)
                        (negative n))
                    (negative (-- n)))
            :by (p/or-intro-right% (or (= n zero)
                                       (negative n))
                                   ((opp-pos-neg n) H3))))
    (have <c> _ :by (p/or-elim% H1 (or (or (= n zero)
                                           (negative n))
                                       (negative (-- n)))
                                <a> <b>)))
  (assume [H4 (positive (-- n))]
    (have <d1> (or (= n zero)
                   (negative n))
          :by (p/or-intro-right% (= n zero)
                                 ((opp-neg-pos-conv n) H4)))
    (have <d> (or (or (= n zero)
                      (negative n))
                  (negative (-- n)))
          :by (p/or-intro-left% <d1> (negative (-- n)))))
  (have <e> _ :by (p/or-elim% (opp-pos-split n)
                              (or (or (= n zero)
                                      (negative n))
                                  (negative (-- n)))
                              <c> <d>))
  (qed <e>))

(defthm opp-nat-split
  [[n int]]
  (==> (elem int (-- n) nat)
       (or (= n zero)
           (negative  n))))

(proof opp-nat-split
    :script
  (assume [H (elem int (-- n) nat)]
    (have <a> (or (= (-- n) zero)
                  (positive (-- n)))
          :by (nat/nat-split (-- n) H))
    (assume [H1 (= (-- n) zero)]
      (have <b1> (= n zero)
            :by ((zero-opp-zero-conv n) H1))
      (have <b> (or (= n zero)
                    (negative n))
            :by (p/or-intro-left% <b1> (negative n))))
    (assume [H2 (positive (-- n))]
      (have <c1> (negative n)
            :by ((opp-neg-pos-conv n) H2))
      (have <c> (or (= n zero)
                    (negative n))
            :by (p/or-intro-right% (= n zero) <c1>)))
    (have <d> _
          :by (p/or-elim% <a> (or (= n zero)
                                  (negative n))
                          <b> <c>)))
  (qed <d>))


(defthm opp-nat-split-conv
  [[n int]]
  (==> (or (= n zero)
           (negative  n))
       (elem int (-- n) nat)))

(proof opp-nat-split-conv
    :script
  (assume [H (or (= n zero)
                 (negative n))]
    (assume [H1 (= n zero)]
      (have <a1> (= zero (-- n))
            :by ((eq/eq-sym int (-- n) zero)
                 ((zero-opp-zero n) H1)))
      (have <a> (elem int (-- n) nat)
            :by (eq/eq-subst% (lambda [k int] (elem int k nat))
                              <a1>
                              (nat/nat-zero))))
    (assume [H2 (negative n)]
      (have <b1> (elem int (pred (-- n)) nat)
            :by ((opp-neg-pos n) H2))
      (have <b2> (elem int (succ (pred (-- n))) nat)
            :by ((nat/nat-succ (pred (-- n))) <b1>))
      (have <b> (elem int (-- n) nat)
            :by (eq/eq-subst% (lambda [k int] (elem int k nat))
                              (int/succ-of-pred (-- n))
                              <b2>)))
    (have <c> _ :by (p/or-elim% H (elem int (-- n) nat)
                                <a> <b>)))
  (qed <c>))

(defthm opp-nat-split-equiv
  [[n int]]
  (<=> (elem int (-- n) nat)
       (or (= n zero)
           (negative  n))))

(proof opp-nat-split-equiv
    :script
  (have <a> _ :by (p/and-intro% (opp-nat-split n)
                                (opp-nat-split-conv n)))
  (qed <a>))

(defthm nat-split-opp
  "A variant of [[nat]] splitting."
  [[n int]]
  (or (elem int n nat)
      (elem int (-- n) nat)))

(proof nat-split-opp
    :script
  (assume [H1 (or (= n zero)
                  (positive n))]
    (assume [H2 (= n zero)]
      (have <a1> (elem int n nat)
            :by ((eq/eq-subst int (lambda [k int] (elem int k nat))
                              zero n)
                 (eq/eq-sym% H2)
                 (nat/nat-zero)))
      (have <a> (or (elem int n nat)
                    (elem int (-- n) nat))
            :by (p/or-intro-left% <a1> (elem int (-- n) nat))))
    (assume [H3 (positive n)]
      (have <b1> (elem int n nat)
            :by ((nat/positive-conv n) H3))
      (have <b> (or (elem int n nat)
                    (elem int (-- n) nat))
            :by (p/or-intro-left% <b1> (elem int (-- n) nat))))
    (have <c> _ :by (p/or-elim% H1 (or (elem int n nat)
                                       (elem int (-- n) nat))
                                <a> <b>)))
  (assume [H4 (negative n)]
    (have <d1> (or (= n zero) (negative n))
          :by (p/or-intro-right% (= n zero) H4))
    (have <d2> (elem int (-- n) nat)
          :by ((opp-nat-split-conv n) <d1>))
    (have <d> _ :by (p/or-intro-right% (elem int n nat) <d2>)))
  "We use int splitting"
  (have <e> _ :by (p/or-elim% (nat/int-split n)
                              (or (elem int n nat)
                                  (elem int (-- n) nat))
                              <c> <d>))
  (qed <e>))

(defthm opp-and-zero
  [[n int]]
  (==> (and (elem int n nat)
            (elem int (-- n) nat))
       (= n zero)))

(proof opp-and-zero
    :script
  (assume [H (and (elem int n nat)
                  (elem int (-- n) nat))]
    (have <a> (elem int n nat) :by (p/and-elim-left% H))
    (have <b> (elem int (-- n) nat) :by (p/and-elim-right% H))
    (assume [H1 (or (= n zero)
                    (positive n))]
      (assume [H2 (= n zero)]
        (have <c> (= n zero) :by H2))
      (assume [H3 (positive n)]
        (have <d1> (negative (-- n))
              :by ((opp-pos-neg n) H3))
        (have <d2> p/absurd :by (<d1> <b>))
        (have <d> (= n zero) :by (<d2> (= n zero))))
      (have <e> (= n zero)
            :by (p/or-elim% H1 (= n zero)
                            <c> <d>)))
    (assume [H4 (negative n)]
      (have <f1> p/absurd :by (H4 <a>))
      (have <f> (= n zero) :by (<f1> (= n zero))))
    "Use integer splitting"
    (have <g> _ :by (p/or-elim% (nat/int-split n)
                                (= n zero)
                                <e> <f>)))
  (qed <g>))


(defthm minus-opp
  "A property about negation of opposites."
  [[n int] [m int]]
  (= (- n m)
     (- (-- m) (-- n))))

(proof minus-opp
    :script
  (have <a> (= (- n m)
               (+ n (-- m)))
        :by (eq/eq-sym% (plus-opp-minus n m)))
  ;; (+ n (-- m))
  (have <b1> (= n (-- (-- n)))
        :by (eq/eq-sym% (opp-opp n)))
  (have <b> (= (- n m)
               (+ (-- (-- n)) (-- m)))
        :by (eq/eq-subst% (lambda [k int] (= (- n m)
                                             (+ k (-- m))))
                          <b1> <a>))
  (have <c> (= (- n m)
               (+ (-- m) (-- (-- n))))
        :by (eq/eq-subst% (lambda [k int] (= (- n m) k))
                          (plus/plus-commute (-- (-- n)) (-- m))
                          <b>))

  (have <d> (= (- n m)
               (- (-- m) (-- n)))
        :by (eq/eq-subst% (lambda [k int] (= (- n m) k))
                          (plus-opp-minus (-- m) (-- n))
                          <c>))

  (qed <d>))


(defthm minus-opp-cancel
  "A cancellation law for subtraction of opposites."
  [[n int] [m int]]
  (==> (= (-- n) (-- m))
       (= n m)))

(proof minus-opp-cancel
    :script
  (assume [H (= (-- n) (-- m))]
    (have <a> (= n m) :by ((minus-left-cancel zero n m) H))
    (qed <a>)))


