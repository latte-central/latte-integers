
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

(definition opp
  "The opposite of an integer."
  [[n int]]
  (- zero n))


