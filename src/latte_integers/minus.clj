
(ns latte-integers.minus
  "The subtraction (and opposite) defined on ℤ."

  (:refer-clojure :exclude [and or not int = + -])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          try-proof qed]]

            [latte.utils :as u]
            
            [latte-prelude.prop :as p :refer [and or not <=>]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.fun :as fun]

            [latte-sets.set :as set :refer [elem]]

            [latte-integers.int :as int :refer [zero one succ pred int =]]
            [latte-integers.nat :as nat :refer [nat positive negative]]
            [latte-integers.rec :as rec]
            [latte-integers.plus :as plus :refer [+]]))

(deflemma minus-ex
  []
  (forall [n m int]
    (exists [p int] (= (+ p m) n))))

(proof 'minus-ex
  (assume [n int]
    "We proceed by induction on `m`."
    "Base case: is `m` is `zero`."
    (have <a1> (= (+ n zero) n)
          :by (plus/plus-zero n))
    (have <a> (exists [p int] (= (+ p zero) n))
          :by ((q/ex-intro (lambda [p int] (= (+ p zero) n))
                           n)
               <a1>))
    "Now the inductive cases"
    (assume [m int
             Hind (exists [p int] (= (+ p m) n))]
      "First the case for `succ`."
      (assume [p int
               Hp (= (+ p m) n)]
        (have <b1> (= (+ p m) (+ (pred p) (succ m)))
              :by (eq/eq-sym (plus/plus-pred-succ p m)))
        (have <b2> (= (+ (pred p) (succ m)) n)
              :by (eq/rewrite Hp <b1>))
        (have <b3> (exists [p int] (= (+ p (succ m)) n))
              :by ((q/ex-intro (lambda [p int] (= (+ p (succ m)) n))
                               (pred p))
                   <b2>))
        "Second the case for `pred`."
        (have <c1> (= (+ p m) (+ (succ p) (pred m)))
              :by (eq/eq-sym (plus/plus-succ-pred p m)))
        (have <c2> (= (+ (succ p) (pred m)) n)
              :by (eq/rewrite (eq/eq-sym <c1>) Hp))
        (have <c3> (exists [p int] (= (+ p (pred m)) n))
              :by ((q/ex-intro (lambda [p int] (= (+ p (pred m)) n))
                               (succ p))
                   <c2>)))
      (have <d1> _ :by (q/ex-elim Hind <b3>))
      (have <d2> _ :by (q/ex-elim Hind <c3>))
      (have <d> _ :by (p/and-intro <d1> <d2>)))
    "We apply integer induction."
    (have <e> (forall [m int]
                (exists [p int] (= (+ p m) n)))
          :by ((int/int-induct (lambda [m int] (exists [p int] (= (+ p m) n))))
               <a> <d>)))
  (qed <e>))

(deflemma minus-single
  [[n int] [m int]]
  (q/single (lambda [p int]
              (= (+ p m) n))))

(proof 'minus-single
  (assume [p1 int
           p2 int
           Hp1 (= (+ p1 m) n)
           Hp2 (= (+ p2 m) n)]
    (have <a> (= (+ p1 m) (+ p2 m))
          :by (eq/eq-trans Hp1 (eq/eq-sym Hp2)))
    (have <b> (= p1 p2)
          :by ((plus/plus-right-cancel p1 p2 m)
               <a>)))
  (have <c> (q/single (lambda [p int] (= (+ p m) n)))
        :by <b>)
  (qed <c>))

(defthm minus-unique
  "The unicity property of subtraction."
  [[n int] [m int]]
  (q/unique (lambda [p int]
              (= (+ p m) n))))

(proof 'minus-unique
  (qed (p/and-intro (minus-ex n m)
                    (minus-single n m))))

(definition -
  "Integer subtraction."
  [[n int] [m int]]
  (q/the (minus-unique n m)))

(defthm minus-prop
  "The defining property of subtraction."
  [[n int] [m int]]
  (= (+ (- n m) m) n))

(proof 'minus-prop
  (qed (q/the-prop (minus-unique n m))))

;; with minus-prop we can hide the definition
(u/set-opacity! #'- true)

(defthm minus-prop-cons
  "A consequence of [[minus-prop]]."
  [[n int] [m int]]
  (= (- (+ n m) m) n))

(proof 'minus-prop-cons
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

(proof 'minus-cancel
  (have <a> (= (+ (- n n) n) n)
        :by (minus-prop n n))
  (have <b> (= n (+ zero n))
        :by (eq/eq-sym (plus/plus-zero-swap n)))
  (have <c> (= (+ (- n n) n)
               (+ zero n))
        :by (eq/eq-trans <a> <b>))
  (have <d> (= (- n n) zero)
        :by ((plus/plus-right-cancel (- n n) zero n)
             <c>))
  (qed <d>))

(defthm minus-zero-alt
  [[m int] [n int]]
  (==> (= (- m n) zero)
       (= m n)))

(proof 'minus-zero-alt
  (assume [H (= (- m n) zero)]
    (have <a> (= (+ (- m n) n)
                 m)
          :by (minus-prop m n))
    (have <b> (= (+ zero n)
                 n)
          :by (plus/plus-zero-swap n))
    (have <c> (= (+ (- m n) n)
                 (+ zero n))
          :by (eq/eq-cong (lambda [k int]
                            (+ k n))
                          H))
    (have <d> (= m (+ zero n))
          :by (eq/rewrite <c> <a>))

    (have <e> (= m n)
          :by (eq/rewrite <d> <b>)))
  (qed <e>))

(defthm minus-zero
  [[n int]]
  (= (- n zero) n))

(proof 'minus-zero
  (have <a> (= (- (+ n zero) zero) n)
        :by (minus-prop-cons n zero))
  (have <b> (= (- n zero) n)
        :by (eq/rewrite <a> (plus/plus-zero n)))
  (qed <b>))

(defthm minus-zero-alt-conv
  [[m int] [n int]]
  (==> (= m n)
       (= (- m n) zero)))

(proof 'minus-zero-alt-conv
  (assume [Hmn (= m n)]
    (have <a> (= (- m n) (- n n))
          :by (eq/eq-cong (lambda [k int] (- k n))
                          Hmn))
    (have <b> (= (- n n) zero)
          :by (minus-cancel n))
    (have <c> (= (- m n) zero)
          :by (eq/rewrite <a> <b>)))
  (qed <c>))

(defthm minus-succ-pred
  [[n int] [m int]]
  (= (- n (succ m))
     (pred (- n m))))

(proof 'minus-succ-pred
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
        :by (eq/eq-trans <b> <c>))
  (have <e> (= n
               (+ (pred (- n m)) (succ m))) :by (eq/eq-sym <d>))
  (have <f> (= (+ (- n (succ m)) (succ m))
               (+ (pred (- n m)) (succ m)))
        :by (eq/eq-trans <a> <e>))
  (have <g> (= (- n (succ m))
               (pred (- n m)))
        :by ((plus/plus-right-cancel (- n (succ m))
                                     (pred (- n m))
                                     (succ m)) <f>))
  (qed <g>))

(defthm minus-succ-pred-sym
  [[n int] [m int]]
  (= (pred (- n m))
     (- n (succ m))))

(proof 'minus-succ-pred-sym
  (qed (eq/eq-sym (minus-succ-pred n m))))

(defthm minus-pred-succ
  [[n int] [m int]]
  (= (- n (pred m))
     (succ (- n m))))

(proof 'minus-pred-succ
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
        :by (eq/eq-trans <b> <c>))
  (have <e> (= n
               (+ (succ (- n m)) (pred m)))
        :by (eq/eq-sym <d>))
  (have <f> (= (+ (- n (pred m)) (pred m))
               (+ (succ (- n m)) (pred m)))
        :by (eq/eq-trans <a> <e>))
  (have <g> (= (- n (pred m))
               (succ (- n m)))
        :by ((plus/plus-right-cancel (- n (pred m))
                                     (succ (- n m))
                                     (pred m)) <f>))
  (qed <g>))

(defthm minus-pred-succ-sym
  [[n int] [m int]]
  (= (succ (- n m))
     (- n (pred m))))

(proof 'minus-pred-succ-sym
  (qed (eq/eq-sym (minus-pred-succ n m))))


(defthm minus-succ
  [[n int] [m int]]
  (= (- (succ n) m)
     (succ (- n m))))

(proof 'minus-succ
  (have <a> (= (+ (- (succ n) m) m)
               (succ n))
        :by (minus-prop (succ n) m))
  (have <b> (= (succ (+ (- n m) m))
               (succ n))
        :by (eq/eq-cong succ (minus-prop n m)))

  (have <c> (= (+ (succ (- n m)) m)
               (succ (+ (- n m) m)))
        :by (plus/plus-succ-swap (- n m) m))
  (have <d> (= (+ (succ (- n m)) m)
               (succ n))
        :by (eq/eq-trans <c> <b>))
  (have <e> (= (succ n)
               (+ (succ (- n m)) m))
        :by (eq/eq-sym <d>))
  (have <f> (= (+ (- (succ n) m) m)
               (+ (succ (- n m)) m))
        :by (eq/eq-trans <a> <e>))
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

(proof 'minus-pred
  (have <a> (= (+ (- (pred n) m) m)
               (pred n))
        :by (minus-prop (pred n) m))
  (have <b> (= (pred (+ (- n m) m))
               (pred n))
        :by (eq/eq-cong pred (minus-prop n m)))
  (have <c> (= (+ (pred (- n m)) m)
               (pred (+ (- n m) m)))
        :by (plus/plus-pred-swap (- n m) m))
  (have <d> (= (+ (pred (- n m)) m)
               (pred n))
        :by (eq/eq-trans <c> <b>))
  (have <e> (= (pred n)
               (+ (pred (- n m)) m))
        :by (eq/eq-sym <d>))
  (have <f> (= (+ (- (pred n) m) m)
               (+ (pred (- n m)) m))
        :by (eq/eq-trans <a> <e>))
  (have <g> (= (- (pred n) m)
               (pred (- n m)))
        :by ((plus/plus-right-cancel (- (pred n) m)
                                     (pred (- n m))
                                     m) <f>))
  (qed <g>))


(defthm minus-one
  [[n int]]
  (= (- n one) (pred n)))

(proof 'minus-one
  (have <a> (= (- n (succ zero))
               (pred (- n zero)))
        :by (minus-succ-pred n zero))
  (have <b> (= (pred (- n zero))
               (pred n))
        :by (eq/eq-cong pred (minus-zero n)))
  (have <c> (= (- n (succ zero))
               (pred n))
        :by (eq/eq-trans <a> <b>))
  (qed <c>))

(defthm minus-right-cancel
  [[n int] [m int] [p int]]
  (==> (= (- n p) (- m p))
       (= n m)))

(proof 'minus-right-cancel
  (assume [H (= (- n p) (- m p))]
    (have <a> (= (+ (- n p) p)
                 (+ (- m p) p))
          :by (eq/eq-cong (lambda [k int] (+ k p))
                           H))
    (have <b> (= (+ (- n p) p) n)
          :by (minus-prop n p))
    (have <c> (= (+ (- m p) p) m)
          :by (minus-prop m p))
    (have <d> (= n (+ (- m p) p))
          :by (eq/rewrite <a> <b>))
    (have <e> (= n m)
          :by (eq/rewrite <d> <c>)))
  (qed <e>))

(defthm minus-left-cancel
  [[n int] [m int] [p int]]
  (==> (= (- n m) (- n p))
       (= m p)))

(proof 'minus-left-cancel
  (assume [H (= (- n m) (- n p))]
    (have <a> (= (+ (- n m) m)
                 (+ (- n p) m))
          :by (eq/eq-cong (lambda [k int] (+ k m)) H))
    (have <b> (= n (+ (- n p) m))
          :by (eq/rewrite <a> (minus-prop n m)))
    (have <c> (= (+ (- n m) p)
                 (+ (- n p) p))
          :by (eq/eq-cong (lambda [k int] (+ k p)) H))
    (have <d> (= (+ (- n m) p) n)
          :by (eq/rewrite <c> (minus-prop n p)))
    (have <e> (= (+ (- n m) p)
                 (+ (- n p) m))
          :by (eq/eq-trans <d> <b>))
    
    (have <f> (= (+ (- n p) p)
                 (+ (- n p) m))
          :by (eq/rewrite <e> H))
    (have <g> (= p m)
          :by ((plus/plus-left-cancel p m (- n p)) <f>))
    (have <h> (= m p) :by (eq/eq-sym <g>)))
  (qed <h>))

(defthm assoc-plus-minus
  [[n int] [m int] [p int]]
  (= (+ n (- m p))
     (- (+ n m) p)))

(proof 'assoc-plus-minus
  (have <a> (= (+ (+ n (- m p)) p)
               (+ n (+ (- m p) p)))
        :by (eq/eq-sym (plus/plus-assoc n (- m p) p)))
  (have <b> (= (+ n (+ (- m p) p))
               (+ n m))
        :by (eq/eq-cong (lambda [k int] (+ n k))
                        (minus-prop m p)))
  (have <c> (= (+ (+ n (- m p)) p)
               (+ n m))
        :by (eq/eq-trans <a> <b>))
  (have <d> (= (+ (- (+ n m) p) p)
               (+ n m)) :by (minus-prop (+ n m) p))
  (have <e> (= (+ n m)
               (+ (- (+ n m) p) p))
        :by (eq/eq-sym <d>))
  (have <f> (= (+ (+ n (- m p)) p)
               (+ (- (+ n m) p) p))
        :by (eq/eq-trans <c> <e>))
  (have <g> (= (+ n (- m p))
               (- (+ n m) p))
        :by ((plus/plus-right-cancel (+ n (- m p))
                                     (- (+ n m) p)
                                     p) <f>))
  (qed <g>))

(defthm assoc-plus-minus-sym
  [[n int] [m int] [p int]]
  (= (- (+ n m) p)
     (+ n (- m p))))

(proof 'assoc-plus-minus-sym
  (qed (eq/eq-sym (assoc-plus-minus n m p))))

(defthm assoc-minus-plus
  [[n int] [m int] [p int]]
  (= (- n (+ m p))
     (- (- n m) p)))

(proof 'assoc-minus-plus
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
        :by (eq/eq-trans <b> <c1>))

  (have <d1> (= (- (+ (+ m p) (- n m)) p)
                (- (- (+ (+ m p) n) m) p))
        :by (eq/eq-cong (lambda [k int] (- k p))
                        (assoc-plus-minus (+ m p) n m)))

  (have <d> (= (+ (- (- n m) p) (+ m p))
               (- (- (+ (+ m p) n) m) p))
        :by (eq/eq-trans <c> <d1>))
  
  (have <e1> (= (- (+ (+ m p) n) m)
                (- (+ (+ p m) n) m))
        :by (eq/eq-cong (lambda [k int] (- (+ k n) m))
                        (plus/plus-commute m p)))
  
  (have <e2> (= (- (+ (+ p m) n) m)
                (- (+ p (+ m n)) m))
        :by (eq/eq-cong (lambda [k int] (- k m))
                        (plus/plus-assoc-sym p m n)))

  (have <e3> (= (- (+ (+ m p) n) m)
                (- (+ p (+ m n)) m))
        :by (eq/eq-trans <e1> <e2>))
  
  (have <e4> (= (- (+ p (+ m n)) m)
                (- (+ p (+ n m)) m))
        :by (eq/eq-cong (lambda [k int] (- (+ p k) m))
                        (plus/plus-commute m n)))

  (have <e5> (= (- (+ (+ m p) n) m)
                (- (+ p (+ n m)) m))
        :by (eq/eq-trans <e3> <e4>))
  
  
  (have <e6> (= (- (+ p (+ n m)) m)
                (- (+ (+ p n) m) m))
        :by (eq/eq-cong (lambda [k int] (- k m))
                        (plus/plus-assoc p n m)))

  (have <e7> (= (- (+ (+ m p) n) m)
                (- (+ (+ p n) m) m))
        :by (eq/eq-trans <e5> <e6>))
  
  (have <e8> (= (- (+ (+ p n) m) m)
                (+ p n))
        :by (minus-prop-cons (+ p n) m))

  (have <e9> (= (- (+ (+ m p) n) m)
                (+ p n))
        :by (eq/eq-trans <e7> <e8>))
 
  ;; hence (- (- (+ (+ p m) n) m) p)
  ;;      = (- (+ p n) p)

  (have <e10> (= (- (- (+ (+ m p) n) m) p)
                 (- (+ p n) p))
        :by (eq/eq-cong (lambda [k int] (- k p))
                        <e9>))

  ;;      = (- (+ n p) p)   by plus-commute

  (have <e11> (= (- (+ p n) p)
               (- (+ n p) p))
        :by (eq/eq-cong (lambda [k int] (- k p))
                        (plus/plus-commute p n)))

  (have <e12> (= (- (+ n p) p)
                 n) :by (minus-prop-cons n p))

  (have <e13> (= (- (+ p n) p)
                 n) :by (eq/eq-trans <e11> <e12>))
  
  (have <e> (= (- (- (+ (+ m p) n) m) p)
               n)
        :by (eq/rewrite <e10> <e13>))

  (have <f1> (= (+ (- (- n m) p) (+ m p))
                n)
        :by (eq/eq-trans <d> <e>))
  
  (have <f> (= n (+ (- (- n m) p) (+ m p)))
        :by (eq/eq-sym <f1>))
  
  
  (have <g> (= (+ (- n (+ m p)) (+ m p))
               (+ (- (- n m) p) (+ m p)))
        :by (eq/eq-trans <a> <f>))

  (have <h> (= (- n (+ m p))
               (- (- n m) p))
        :by ((plus/plus-right-cancel (- n (+ m p))
                                     (- (- n m) p)
                                     (+ m p))
             <g>))
  
  (qed <h>))

(defthm assoc-minus-plus-sym
  [[n int] [m int] [p int]]
  (= (- (- n m) p)
     (- n (+ m p))))

(proof 'assoc-minus-plus-sym
  (qed (eq/eq-sym (assoc-minus-plus n m p))))


(defthm assoc-minus-minus
  [[n int] [m int] [p int]]
  (= (- n (- m p))
     (+ (- n m) p)))

(proof 'assoc-minus-minus
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
        :by (eq/eq-trans <b> <c1>))

  (have <d1> (= (+ (- m p) (- n m))
                (+ (- n m) (- m p)))
        :by (plus/plus-commute (- m p) (- n m)))
  (have <d2> (= (+ (- n m) (- m p))
                (- (+ (- n m) m) p))
        :by (assoc-plus-minus (- n m) m p))
  (have <d3> (= (+ (- m p) (- n m))
                (- (+ (- n m) m) p))
        :by (eq/eq-trans <d1> <d2>))
  (have <d> (= (+ (- m p) (- n m))
               (- n p))
        :by (eq/rewrite <d3> (minus-prop n m)))

  (have <e1> (= (+ (+ (- n m) p) (- m p))
                (+ (- n p) p))
        :by (eq/rewrite <c> <d>))

  (have <e2> (= (+ (+ (- n m) p) (- m p))
               n)
        :by (eq/rewrite <e1> (minus-prop n p)))

  (have <e> (= n (+ (+ (- n m) p) (- m p)))
        :by (eq/eq-sym <e2>))

  (have <f> (= (+ (- n (- m p)) (- m p))
               (+ (+ (- n m) p) (- m p)))
        :by (eq/eq-trans <a> <e>))

  (have <g> (= (- n (- m p))
               (+ (- n m) p))
        :by ((plus/plus-right-cancel (- n (- m p))
                                     (+ (- n m) p)
                                     (- m p)) <f>))
  (qed <g>))

(defthm assoc-minus-minus-sym
  [[n int] [m int] [p int]]
  (= (+ (- n m) p)
     (- n (- m p))))

(proof 'assoc-minus-minus-sym
  (qed (eq/eq-sym (assoc-minus-minus n m p))))

(defthm minus-pos-neg
  [[n int] [m int]]
  (==> (positive (- n m))
       (negative (- m n))))

(proof 'minus-pos-neg
  (assume [Hpos (positive (- n m))]
    (assume [Hnat (elem (- m n) nat)]
      (have <a> (elem (+ (pred (- n m)) (- m n)) nat)
            :by (plus/plus-nat-closed (pred (- n m)) Hpos
                                      (- m n) Hnat))
      (have <b1> (= (+ (pred (- n m)) (- m n))
                    (pred (+ (- n m) (- m n))))
            :by (plus/plus-pred-swap (- n m) (- m n)))

      (have <b2> (= (pred (+ (- n m) (- m n)))
                    (pred (- (+ (- n m) m) n)))
            :by (eq/eq-cong pred
                            (assoc-plus-minus (- n m) m n)))
      (have <b3> (= (+ (pred (- n m)) (- m n))
                    (pred (- (+ (- n m) m) n)))
            :by (eq/eq-trans <b1> <b2>))
      
      (have <b4> (= (pred (- (+ (- n m) m) n))
                    (pred (- n n)))
            :by (eq/eq-cong (lambda [k int] (pred (- k n)))
                            (minus-prop n m)))

      (have <b5> (= (+ (pred (- n m)) (- m n))
                    (pred (- n n)))
            :by (eq/eq-trans <b3> <b4>))
      
      (have <b6> (= (+ (pred (- n m)) (- m n))
                    (pred zero))
            :by (eq/rewrite <b5> (minus-cancel n)))

      (have <b> (elem (pred zero) nat)
            :by (eq/rewrite <a> <b6>))

      (have <c> p/absurd :by (nat/negative-pred-zero <b>))))
  (qed <c>))

(defthm plus-zero-minus
  [[n int] [m int]]
  (= (+ (- zero n) m)
     (- m n)))

(proof 'plus-zero-minus
  (have <a> (= (+ (- zero n) m)
               (+ m (- zero n)))
        :by (plus/plus-commute (- zero n) m))
  (have <b> (= (+ m (- zero n))
               (- (+ m zero) n)) :by (assoc-plus-minus m zero n))
  (have <c> (= (+ (- zero n) m)
               (- (+ m zero) n)) :by (eq/eq-trans <a> <b>))
  (have <d> (= (- (+ m zero) n)
               (- m n))
        :by (eq/eq-cong (lambda [k int] (- k n))
                        (plus/plus-zero m)))
  (have <e> (= (+ (- zero n) m)
               (- m n)) :by (eq/eq-trans <c> <d>))
  (qed <e>))

(defthm minus-pos-neg-conv
  [[n int] [m int]]
  (==> (negative (- m n))
       (positive (- n m))))

(proof 'minus-pos-neg-conv
  (assume [Hneg (negative (- m n))]
    (have <a> (exists [p int]
                (and (positive p) (= (+ (- m n) p) zero)))
          :by ((plus/negative-pos-plus (- m n))
               Hneg))
    (assume [p int
             Hp (and (positive p)
                     (= (+ (- m n) p) zero))]
      (have <b> (positive p) :by (p/and-elim-left Hp))
      (have <c> (= (+ (- m n) p) zero) :by (p/and-elim-right Hp))

      (have <d> (= (+ p (- m n)) zero)
            :by (eq/rewrite <c> (plus/plus-commute (- m n) p)))

      (have <e> (= (- (+ p (- m n)) (- m n))
                   (- zero (- m n)))
            :by (eq/eq-cong (lambda [k int] (- k (- m n)))
                            <d>))

      (have <f> (= p (- zero (- m n)))
            :by (eq/rewrite <e> (minus-prop-cons p (- m n))))

      (have <g> (= p (+ (- zero m) n))
            :by (eq/rewrite <f> (assoc-minus-minus zero m n)))

      (have <h> (= p (- n m))
            :by (eq/rewrite <g> (plus-zero-minus m n)))

      (have <i> (positive (- n m))
            :by (eq/rewrite <b> <h>)))
    (have <j> (positive (- n m))
          :by (q/ex-elim <a> <i>)))
  (qed <j>))

(defthm minus-pos-neg-equiv
  [[n int] [m int]]
  (<=> (positive (- n m))
       (negative (- m n))))

(proof 'minus-pos-neg-equiv
  (qed (p/and-intro (minus-pos-neg n m) (minus-pos-neg-conv n m))))

(definition --
  "The opposite of an integer."
  [[n int]]
  (- zero n))

(defthm opp-unfold
  "The unfolding of the opposite or `n` (because it is opaque)."
  [[n int]]
  (= (-- n) (- zero n)))

(proof 'opp-unfold
  (qed (eq/eq-refl (-- n))))

(defthm opp-plus-opp
  [[n int]]
  (= (+ (-- n) n)
     zero))

(proof 'opp-plus-opp
  (have <a> (= (+ (-- n) n)
               (+ n (- zero n)))
        :by (plus/plus-commute (-- n) n))

  (have <b1> (= (+ n (- zero n))
                (- (+ n zero) n))
        :by (assoc-plus-minus n zero n))

  (have <b> (= (+ (-- n) n)
               (- (+ n zero) n))
        :by (eq/eq-trans <a> <b1>))
  
  (have <c1> (= (- (+ n zero) n)
                (- n n))
        :by (eq/eq-cong (lambda [k int] (- k n))
                        (plus/plus-zero n)))

  (have <c> (= (+ (-- n) n)
               (- n n))
        :by (eq/eq-trans <b> <c1>))
  
  (have <d> (= (+ (-- n) n)
               zero)
        :by (eq/rewrite <c> (minus-cancel n)))
  (qed <d>))

(defthm plus-opp-minus
  [[n int] [m int]]
  (= (+ n (-- m))
     (- n m)))

(proof 'plus-opp-minus
  (have <a> (= (+ n (- zero m))
               (- (+ n zero) m))
        :by (assoc-plus-minus n zero m))

  (have <b> (= (+ n (-- m))
               (- n m))
        :by (eq/rewrite <a> (plus/plus-zero n)))
  (qed <b>))

(defthm opp-plus
  [[n int] [m int]]
  (= (-- (+ n m))
     (- (-- n) m)))

(proof 'opp-plus
  (have <a> (= (- zero (+ n m))
               (- (- zero n) m))
        :by (assoc-minus-plus zero n m))
  (qed <a>))


(defthm opp-zero
  []
  (= (-- zero) zero))

(proof 'opp-zero
  (have <a> (= (- zero zero)
               zero)
        :by (minus-zero zero))
  (qed <a>))

(defthm opp-opp
  [[n int]]
  (= (-- (-- n))
     n))

(proof 'opp-opp
  (have <a> (= (- zero (- zero n))
               (+ (- zero zero) n))
        :by (assoc-minus-minus zero zero n))
  (have <b> (= (-- (-- n))
               (+ zero n))
        :by (eq/rewrite <a> (minus-zero zero)))
  (have <c> (= (-- (-- n))
               n)
        :by (eq/rewrite <b> (plus/plus-zero-swap n)))
  (qed <c>))

(defthm zero-opp-zero
  [[n int]]
  (==> (= n zero)
       (= (-- n) zero)))

(proof 'zero-opp-zero
  (assume [H (= n zero)]
    (have <a> (= (-- n) (-- zero))
          :by (eq/eq-cong (lambda [k int] (-- k))
                          H))
    (have <b> (= (-- n) zero)
          :by (eq/rewrite <a> opp-zero)))
  (qed <b>))

(defthm zero-opp-zero-conv
  [[n int]]
  (==> (= (-- n) zero)
       (= n zero)))

(proof 'zero-opp-zero-conv
  (assume [H (= (-- n) zero)]
    (have <a> (= (+ (-- n) n)
                 (+ zero n))
          :by ((plus/plus-right-cancel-conv (-- n) zero n)
               H))
    (have <b> (= zero
                 (+ zero n))
          :by (eq/rewrite <a> (opp-plus-opp n)))
    
    (have <c> (= zero n)
          :by (eq/rewrite <b> (plus/plus-zero-swap n)))
    
    (have <d> (= n zero) :by (eq/eq-sym <c>)))
  (qed <d>))


(defthm zero-opp-zero-equiv
  [[n int]]
  (<=> (= n zero)
       (= (-- n) zero)))

(proof 'zero-opp-zero-equiv
  (qed (p/iff-intro  (zero-opp-zero n)
                     (zero-opp-zero-conv n))))


(defthm opp-succ-pred
  [[n int]]
  (= (-- (succ n))
     (pred (-- n))))

(proof 'opp-succ-pred
  (qed (minus-succ-pred zero n)))


(defthm opp-pred-succ
  [[n int]]
  (= (-- (pred n))
     (succ (-- n))))

(proof 'opp-pred-succ
  (qed (minus-pred-succ zero n)))


(defthm opp-pos-neg
  [[n int]]
  (==> (positive n)
       (negative (-- n))))

(proof 'opp-pos-neg
  (assume [H (positive n)]
    (have <a> (positive (- n zero))
          :by (eq/rewrite H (eq/eq-sym (minus-zero n))))
    (have <b> (negative (- zero n))
          :by ((minus-pos-neg n zero) <a>)))
  (qed <b>))

(defthm opp-pos-neg-conv
  [[n int]]
  (==> (negative (-- n))
       (positive n)))

(proof 'opp-pos-neg-conv
  (assume [H (negative (-- n))]
    (have <a> (positive (- n zero))
          :by ((minus-pos-neg-conv n zero) H))
    (have <b> (positive n)
          :by (eq/rewrite <a> (minus-zero n))))
  (qed <b>))

(defthm opp-pos-neg-equiv
  [[n int]]
  (<=> (positive n)
       (negative (-- n))))

(proof 'opp-pos-neg-equiv
  (qed (p/iff-intro (opp-pos-neg n)
                    (opp-pos-neg-conv n))))


(defthm opp-neg-pos
  [[n int]]
  (==> (negative n)
       (positive (-- n))))

(proof 'opp-neg-pos
  (assume [H (negative n)]
    (have <a> (negative (-- (-- n)))
          :by (eq/rewrite H (eq/eq-sym (opp-opp n))))
    (have <b> (positive (-- n))
          :by ((opp-pos-neg-conv (-- n)) <a>)))
  (qed <b>))

(defthm opp-neg-pos-conv
  [[n int]]
  (==> (positive (-- n))
       (negative n)))

(proof 'opp-neg-pos-conv
  (assume [H (positive (-- n))]
    (have <a> (negative (-- (-- n)))
          :by ((opp-pos-neg (-- n)) H))
    (have <b> (negative n)
          :by (eq/rewrite <a> (opp-opp n))))
  (qed <b>))

(defthm opp-neg-pos-equiv
  [[n int]]
  (<=> (negative n)
       (positive (-- n))))

(proof 'opp-neg-pos-equiv
  (qed (p/iff-intro (opp-neg-pos n)
                    (opp-neg-pos-conv n))))
  
(defthm opp-pos-split
  "A split for integers using the opposite, using [[nat/positive]]."
  [[n int]]
  (or (or (= n zero)
          (positive n))
      (positive (-- n))))

(proof 'opp-pos-split
  (assume [H1 (or (= n zero)
                  (positive n))]
    (have <a> (or (or (= n zero)
                      (positive n))
                  (positive (-- n)))
          :by (p/or-intro-left H1
                               (positive (-- n)))))
  (assume [H2 (negative n)]
    (have <b1> (positive (-- n))
          :by ((opp-neg-pos n) H2))
    (have <b> (or (or (= n zero)
                      (positive n))
                  (positive (-- n)))
          :by (p/or-intro-right (or (= n zero)
                                    (positive n))
                                <b1>)))
  (have <c> (or (or (= n zero)
                    (positive n))
                (positive (-- n)))
        :by (p/or-elim (nat/int-split n) <a> <b>))
  (qed <c>))

(defthm opp-neg-split
  "A split for integers using the opposite, using [[nat/negative]]."
  [[n int]]
  (or (or (= n zero)
          (negative n))
      (negative (-- n))))

(proof 'opp-neg-split
  (assume [H1 (or (= n zero)
                  (positive n))]
    (assume [H2 (= n zero)]
      (have <a1> (or (= n zero)
                     (negative n))
            :by (p/or-intro-left H2 (negative n)))
      (have <a> (or (or (= n zero)
                        (negative n))
                    (negative (-- n)))
            :by (p/or-intro-left <a1> (negative (-- n)))))
    (assume [H3 (positive n)]
      (have <b> (or (or (= n zero)
                        (negative n))
                    (negative (-- n)))
            :by (p/or-intro-right (or (= n zero)
                                       (negative n))
                                   ((opp-pos-neg n) H3))))
    (have <c> (or (or (= n zero)
                      (negative n))
                  (negative (-- n))) 
          :by (p/or-elim H1 <a> <b>)))
  (assume [H4 (positive (-- n))]
    (have <d1> (or (= n zero)
                   (negative n))
          :by (p/or-intro-right (= n zero)
                                 ((opp-neg-pos-conv n) H4)))
    (have <d> (or (or (= n zero)
                      (negative n))
                  (negative (-- n)))
          :by (p/or-intro-left <d1> (negative (-- n)))))
  (have <e> (or (or (= n zero)
                    (negative n))
                (negative (-- n))) 
        :by (p/or-elim (opp-pos-split n) <c> <d>))
  (qed <e>))

(defthm opp-nat-split
  [[n int]]
  (==> (elem (-- n) nat)
       (or (= n zero)
           (negative  n))))

(proof 'opp-nat-split
  (assume [H (elem (-- n) nat)]
    (have <a> (or (= (-- n) zero)
                  (positive (-- n)))
          :by (nat/nat-split (-- n) H))
    (assume [H1 (= (-- n) zero)]
      (have <b1> (= n zero)
            :by ((zero-opp-zero-conv n) H1))
      (have <b> (or (= n zero)
                    (negative n))
            :by (p/or-intro-left <b1> (negative n))))
    (assume [H2 (positive (-- n))]
      (have <c1> (negative n)
            :by ((opp-neg-pos-conv n) H2))
      (have <c> (or (= n zero)
                    (negative n))
            :by (p/or-intro-right (= n zero) <c1>)))
    (have <d> (or (= n zero)
                  (negative n))
          :by (p/or-elim <a> <b> <c>)))
  (qed <d>))


(defthm opp-nat-split-conv
  [[n int]]
  (==> (or (= n zero)
           (negative  n))
       (elem (-- n) nat)))

(proof 'opp-nat-split-conv
  (assume [H (or (= n zero)
                 (negative n))]
    (assume [H1 (= n zero)]
      (have <a1> (= zero (-- n))
            :by (eq/eq-sym ((zero-opp-zero n) H1)))
      (have <a> (elem (-- n) nat)
            :by (eq/rewrite (nat/nat-zero) <a1>)))

    (assume [H2 (negative n)]
      (have <b1> (elem (pred (-- n)) nat)
            :by ((opp-neg-pos n) H2))
      (have <b2> (elem (succ (pred (-- n))) nat)
            :by ((nat/nat-succ (pred (-- n))) <b1>))
      (have <b> (elem (-- n) nat)
            :by (eq/rewrite <b2> (int/succ-of-pred (-- n)))))
    (have <c> (elem (-- n) nat) :by (p/or-elim H <a> <b>)))
  (qed <c>))

(defthm opp-nat-split-equiv
  [[n int]]
  (<=> (elem (-- n) nat)
       (or (= n zero)
           (negative  n))))

(proof 'opp-nat-split-equiv
  (qed (p/iff-intro (opp-nat-split n)
                    (opp-nat-split-conv n))))

(defthm nat-split-opp
  "A variant of [[nat]] splitting."
  [[n int]]
  (or (elem n nat)
      (elem (-- n) nat)))

(proof 'nat-split-opp
  (assume [H1 (or (= n zero)
                  (positive n))]
    (assume [H2 (= n zero)]
      (have <a1> (elem n nat)
            :by (eq/rewrite (nat/nat-zero) (eq/eq-sym H2)))
      (have <a> (or (elem n nat)
                    (elem (-- n) nat))
            :by (p/or-intro-left <a1> (elem (-- n) nat))))
    (assume [H3 (positive n)]
      (have <b1> (elem n nat)
            :by ((nat/positive-conv n) H3))
      (have <b> (or (elem n nat)
                    (elem (-- n) nat))
            :by (p/or-intro-left <b1> (elem (-- n) nat))))
    (have <c> (or (elem n nat)
                  (elem (-- n) nat))
          :by (p/or-elim H1 <a> <b>)))
  (assume [H4 (negative n)]
    (have <d1> (or (= n zero) (negative n))
          :by (p/or-intro-right (= n zero) H4))
    (have <d2> (elem (-- n) nat)
          :by ((opp-nat-split-conv n) <d1>))
    (have <d> _ :by (p/or-intro-right (elem n nat) <d2>)))
  "We use int splitting"
  (have <e> (or (elem n nat)
                (elem (-- n) nat)) 
        :by (p/or-elim (nat/int-split n) <c> <d>))
  (qed <e>))

(defthm opp-and-zero
  [[n int]]
  (==> (and (elem n nat)
            (elem (-- n) nat))
       (= n zero)))

(proof 'opp-and-zero
  (assume [H (and (elem n nat)
                  (elem (-- n) nat))]
    (have <a> (elem n nat) :by (p/and-elim-left H))
    (have <b> (elem (-- n) nat) :by (p/and-elim-right H))
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
            :by (p/or-elim H1 <c> <d>)))
    (assume [H4 (negative n)]
      (have <f1> p/absurd :by (H4 <a>))
      (have <f> (= n zero) :by (<f1> (= n zero))))
    "Use integer splitting"
    (have <g> (= n zero) :by (p/or-elim (nat/int-split n) <e> <f>)))
  (qed <g>))


(defthm minus-opp
  "A property about negation of opposites."
  [[n int] [m int]]
  (= (- n m)
     (- (-- m) (-- n))))

(proof 'minus-opp
  (have <a> (= (- n m)
               (+ n (-- m)))
        :by (eq/eq-sym (plus-opp-minus n m)))
  ;; (+ n (-- m))
  (have <b1> (= n (-- (-- n)))
        :by (eq/eq-sym (opp-opp n)))
  (have <b> (= (- n m)
               (+ (-- (-- n)) (-- m)))
        :by (eq/nrewrite 2 <a> <b1>))
  (have <c> (= (- n m)
               (+ (-- m) (-- (-- n))))
        :by (eq/rewrite <b> (plus/plus-commute (-- (-- n)) (-- m))))

  (have <d> (= (- n m)
               (- (-- m) (-- n)))
        :by (eq/rewrite <c> (plus-opp-minus (-- m) (-- n))))
  
  (qed <d>))


(defthm minus-opp-cancel
  "A cancellation law for subtraction of opposites."
  [[n int] [m int]]
  (==> (= (-- n) (-- m))
       (= n m)))

(proof 'minus-opp-cancel
  (assume [H (= (-- n) (-- m))]
    (have <a> (= n m) :by ((minus-left-cancel zero n m) H)))
  (qed <a>))

(defthm opp-eq
  [[m int] [n int]]
  (==> (= (-- m) n)
       (= m (-- n))))

(proof 'opp-eq
  (assume [H (= (-- m) n)]
    (have <a> (= n (-- (-- n)))
          :by (eq/eq-sym (opp-opp n)))
    (have <b> (= (-- m) (-- (-- n)))
          :by (eq/rewrite H <a>))
    (have <c> (= m (-- n))
          :by ((minus-opp-cancel m (-- n)) <b>)))
  (qed <c>))

;; The opposite is now made opaque
(u/set-opacity! #'-- true)
