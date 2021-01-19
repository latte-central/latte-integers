(ns latte-integers.ord

  "The natural ordering on integers."

  (:refer-clojure :exclude [and or not int = + - < <= > >=])

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
            [latte-sets.quant :as sq :refer [exists-in]]

            [latte-integers.int :as int :refer [zero one succ pred int =]]
            [latte-integers.nat :as nat :refer [nat positive negative]]
            [latte-integers.rec :as rec]
            [latte-integers.plus :as plus :refer [+]]
            [latte-integers.minus :as minus :refer [- --]]))

(definition <=
  "The lower-or-equal order for integers."
  [[n int] [m int]]
  (elem (- m n) nat))

;; The following intro and elim rules
;; are useful because <= is opaque (outside this namespace)

(defthm le-intro
  [[n int] [m int]]
  (==> (elem (- m n) nat)
       (<= n m)))

(proof 'le-intro
  (assume [H _]
    (have <a> _ :by H))
  (qed <a>))

(defthm le-elim
  [[n int] [m int]]
  (==> (<= n m)
       (elem (- m n) nat)))

(proof 'le-elim
  (assume [H _]
    (have <a> _ :by H))
  (qed <a>))
  

(defthm le-refl
  [[n int]]
  (<= n n))

(proof 'le-refl
  (have <a> (= zero (- n n))
        :by (eq/eq-sym (minus/minus-cancel n)))
  (have <b> (<= n n)
        :by (eq/rewrite (nat/nat-zero) <a>))
  (qed <b>))

(defthm le-trans
  [[n int] [m int] [p int]]
  (==> (<= n m)
       (<= m p)
       (<= n p)))

(proof 'le-trans
  (assume [Hnm (<= n m)
           Hmp (<= m p)]

    (have <a> (elem (+ (- m n) (- p m)) nat)
          :by (plus/plus-nat-closed (- m n) Hnm
                                    (- p m) Hmp))

    (have <b> (elem (+ (- p m) (- m n)) nat)
          :by (eq/rewrite <a> (plus/plus-commute (- m n) (- p m))))

    (have <c> (elem (- (+ (- p m) m) n) nat)
          :by (eq/rewrite <b> (minus/assoc-plus-minus (- p m) m n)))

    (have <d> (<= n p)
          :by (eq/rewrite <c> (minus/minus-prop p m))))
  (qed <d>))

(defthm le-antisym
  [[n int] [m int]]
  (==> (<= n m)
       (<= m n)
       (= n m)))

(proof 'le-antisym
  (assume [Hnm (<= n m)  ;; (elem (- m n) nat)
           Hmn (<= m n)] ;; (elem (- n m) nat)

    ;; (or (= (- m n) zero) (positive (- m n)))
    (assume [H1 (= (- m n) zero)]
      (have <a1> (= (+ (- m n) n)
                    (+ zero n))
            :by (eq/eq-cong (lambda [k int] (+ k n))
                            H1))
      (have <a2> (= m (+ zero n))
            :by (eq/rewrite <a1> (minus/minus-prop m n)))

      (have <a3> (= m n)
            :by (eq/rewrite <a2> (plus/plus-zero-swap n)))

      (have <a> (= n m) :by (eq/eq-sym <a3>)))
    (assume [H2 (positive (- m n))]
      (have <b1> (negative (- n m))
            :by ((minus/minus-pos-neg m n) H2))
      (have <b2> p/absurd :by (<b1> Hmn))
      (have <b> (= n m) :by (<b2> (= n m))))
    "We use the nat splitting principle."
    (have <c> (or (= (- m n) zero)
                  (positive (- m n)))
          :by (nat/nat-split (- m n) Hnm))
    (have <d> (= n m) :by (p/or-elim <c> <a> <b>)))
  (qed <d>))

(definition <
  "The strict variant of [[<=]]."
  [[n int] [m int]]
  (and (<= n m)
       (not (= n m))))

(defthm lt-asym
  [[n int] [m int]]
  (==> (< n m)
       (not (< m n))))

(proof 'lt-asym
  (assume [Hnm (< n m)]
    (assume [Hmn (< m n)]
      (have <a> (= n m)
            :by ((le-antisym n m)
                 (p/and-elim-left Hnm)
                 (p/and-elim-left Hmn)))
      (have <b> p/absurd :by ((p/and-elim-right Hnm) <a>))))
  (qed <b>))

(defthm lt-trans
  [[n int] [m int] [p int]]
  (==> (< n m)
       (< m p)
       (< n p)))

(proof 'lt-trans
  (assume [Hnm (< n m)
           Hmp (< m p)]
    (have <a> (<= n m) :by (p/and-elim-left Hnm))
    (have <b> (not (= n m)) :by (p/and-elim-right Hnm))
    (have <c> (<= m p) :by (p/and-elim-left Hmp))
    (have <d> (not (= m p)) :by (p/and-elim-right Hmp))
    (have <e> (<= n p) :by ((le-trans n m p) <a> <c>))
    (assume [Hcut (= n p)]
      (have <f1> (< p m)
            :by (eq/rewrite Hnm Hcut))
      (have <f2> (not (< p m)) :by ((lt-asym m p) Hmp))
      (have <f> p/absurd :by (<f2> <f1>)))
    (have <g> (< n p)
          :by (p/and-intro <e> <f>)))
  (qed <g>))

(defthm lt-trans-weak
  [[n int] [m int] [p int]]
  (==> (<= n m)
       (< m p)
       (< n p)))

(proof 'lt-trans-weak
  (assume [Hnm (<= n m)
           Hmp (< m p)]
    (have <a> (<= m p) :by (p/and-elim-left Hmp))
    (have <b> (not (= m p)) :by (p/and-elim-right Hmp))
    (have <c> (<= n p) :by ((le-trans n m p) Hnm <a>))
    (assume [H (= n p)]
      (have <d1> (<= p m) :by (eq/rewrite Hnm H))
      (have <d2> (= m p) :by ((le-antisym m p) <a> <d1>))
      (have <d> p/absurd :by (<b> <d2>)))
    (have <e> (< n p) :by (p/and-intro <c> <d>)))
  (qed <e>))

(defthm lt-trans-weak-alt
  "An alternative to [[lt-trans-weak]]."
  [[n int] [m int] [p int]]
  (==> (< n m)
       (<= m p)
       (< n p)))

(proof 'lt-trans-weak-alt
  (assume [Hnm (< n m)
           Hmp (<= m p)]
    (have <a> (<= n m) :by (p/and-elim-left Hnm))
    (have <b> (not (= n m)) :by (p/and-elim-right Hnm))
    (have <c> (<= n p) :by ((le-trans n m p) <a> Hmp))
    (assume [H (= n p)]
      (have <d1> (= p n) :by (eq/eq-sym H))
      (have <d2> (<= m n) :by (eq/rewrite Hmp <d1>))
      (have <d3> (= n m) :by ((le-antisym n m) <a> <d2>))
      (have <d> p/absurd :by (<b> <d3>)))
    (have <e> (< n p) :by (p/and-intro <c> <d>)))
  (qed <e>))


(defthm le-lt-split
  [[m int] [n int]]
  (==> (<= m n)
       (or (= m n)
           (< m n))))

(proof 'le-lt-split
  (assume [Hmn (<= m n)]
    (assume [H1 (= (- m n) zero)]
      (have <a1> (= m n)
            :by ((minus/minus-zero-alt m n) H1))
      (have <a> _ :by (p/or-intro-left <a1> (< m n))))
    (assume [H2 (not (= (- m n) zero))]
      (assume [Heq (= m n)]
        (have <b1> (= (- m n) zero)
              :by ((minus/minus-zero-alt-conv m n) Heq))
        (have <b> p/absurd :by (H2 <b1>)))
      (have <c1> (< m n)
            :by (p/and-intro Hmn <b>))
      (have <c> _ :by (p/or-intro-right (= m n) <c1>)))
    (have <d> (or (= m n)
                  (< m n)) 
          :by (p/or-elim (nat/int-split-zero (- m n)) <a> <c>)))
  (qed <d>))

(defthm lt-le
  [[m int] [n int]]
  (==> (< m n)
       (<= m n)))

(proof 'lt-le
  (assume [Hmn (< m n)]
    (have <a> (<= m n)
          :by (p/and-elim-left Hmn)))
  (qed <a>))

(defthm plus-le
  [[n int] [m int] [p int]]
  (==> (<= (+ n p) (+ m p))
       (<= n m)))

(proof 'plus-le
  (assume [H (<= (+ n p) (+ m p))]
    (have <a> (elem (- (+ m p) (+ p n)) nat)
          :by (eq/rewrite H (plus/plus-commute n p)))
    (have <b> (elem (- (- (+ m p) p) n) nat)
          :by (eq/rewrite <a> (minus/assoc-minus-plus (+ m p) p n)))
    (have <c> (<= n m)
          :by (eq/rewrite <b> (minus/minus-prop-cons m p))))
  (qed <c>))

(defthm plus-le-conv
  "The converse of [[plus-le]]."
  [[n int] [m int] [p int]]
  (==> (<= n m)
       (<= (+ n p) (+ m p))))

(proof 'plus-le-conv
  (assume [H (<= n m)]

    (have <a1> (= (- m n) (+ (- m n) zero))
          :by (eq/eq-sym (plus/plus-zero (- m n))))
    (have <a2> (= zero (- p p))
          :by (eq/eq-sym (minus/minus-cancel p)))
    (have <a3> (= (- m n) (+ (- m n) (- p p)))
          :by (eq/rewrite <a1> <a2>))
    (have <a> (elem (+ (- m n) (- p p)) nat)
          :by (eq/rewrite H <a3>))

    (have <b> (elem (- (+ (- m n) p) p) nat)
          :by (eq/rewrite <a> (minus/assoc-plus-minus (- m n) p p)))

    (have <c> (elem (- (+ p (- m n)) p) nat)
          :by (eq/rewrite <b> (plus/plus-commute (- m n) p)))

    (have <d> (elem (- (- (+ p m) n) p) nat)
          :by (eq/rewrite <c> (minus/assoc-plus-minus p m n)))

    (have <e> (= (- (- (+ p m) n) p)
                 (- (+ p m) (+ n p)))
          :by (eq/eq-sym (minus/assoc-minus-plus (+ p m) n p)))

    (have <f> (= (- (- (+ p m) n) p)
                 (- (+ m p) (+ n p)))
          :by (eq/nrewrite 2 <e> (plus/plus-commute p m)))

    (have <g> (elem (- (+ m p) (+ n p)) nat)
          :by (eq/rewrite <d> <f>)))

  (qed <g>))

(defthm plus-le-equiv
  [[n int] [m int] [p int]]
  (<=> (<= (+ n p) (+ m p))
       (<= n m)))

(proof 'plus-le-equiv
  (qed (p/iff-intro (plus-le n m p)
                    (plus-le-conv n m p))))

(defthm plus-le-prop
  "This is useful to relate `<=` to addition."
  [[n int] [m int]]
  (==> (<= n m)
       (exists-in [k nat]
         (= (+ n k) m))))

(proof 'plus-le-prop
  (assume [H _]
    (have <a> (elem (- m n) nat) :by H)
    (have <b> (= (+ (- m n) n) m)
          :by (minus/minus-prop m n))
    (have <c> (= (+ n (- m n)) m)
          :by (eq/rewrite <b> (plus/plus-commute (- m n) n)))
    (have <d> _ :by ((q/ex-intro (lambda [k int]
                                   (and (elem k nat)
                                        (= (+ n k) m))) (- m n))
                     (p/and-intro <a> <c>))))
  (qed <d>))

(defthm plus-lt
  [[n int] [m int] [p int]]
  (==> (< (+ n p) (+ m p))
       (< n m)))

(proof 'plus-lt
  (assume [H (< (+ n p) (+ m p))]
    (have <a> (<= (+ n p) (+ m p))
          :by (p/and-elim-left H))
    (have <b> (not (= (+ n p) (+ m p)))
          :by (p/and-elim-right H))
    (have <c> (<= n m)
          :by ((plus-le n m p) <a>))
    (assume [H2 (= n m)]
      (have <d1> (= (+ n p) (+ m p))
            :by ((plus/plus-right-cancel-conv n m p) H2))
      (have <d> p/absurd :by (<b> <d1>)))
    (have <e> (< n m)
          :by (p/and-intro <c> <d>)))
  (qed <e>))

(defthm plus-lt-conv
  [[n int] [m int] [p int]]
  (==> (< n m)
       (< (+ n p) (+ m p))))

(proof 'plus-lt-conv
  (assume [H (< n m)]
    (have <a> (<= n m) :by (p/and-elim-left H))
    (have <b> (not (= n m)) :by (p/and-elim-right H))
    (have <c> (<= (+ n p) (+ m p))
          :by ((plus-le-conv n m p) <a>))
    (assume [H2 (= (+ n p) (+ m p))]
      (have <d1> (= n m) :by ((plus/plus-right-cancel n m p) H2))
      (have <d> p/absurd :by (<b> <d1>)))
    (have <e> (< (+ n p) (+ m p))
          :by (p/and-intro <c> <d>)))
  (qed <e>))

(defthm plus-lt-equiv
  [[n int] [m int] [p int]]
  (<=> (< (+ n p) (+ m p))
       (< n m)))

(proof 'plus-lt-equiv
  (qed (p/iff-intro (plus-lt n m p)
                    (plus-lt-conv n m p))))

(defthm plus-le-cong
  [[m1 int] [m2 int] [n1 int] [n2 int]]
  (==> (<= m1 n1)
       (<= m2 n2)
       (<= (+ m1 m2) (+ n1 n2))))

(proof 'plus-le-cong
  (assume [H1 (<= m1 n1)
           H2 (<= m2 n2)]
    (have <a> (elem (- n1 m1) nat) :by H1)
    (have <b> (elem (- n2 m2) nat) :by H2)
    (have <c> (elem (+ (- n1 m1) (- n2 m2)) nat)
          :by (plus/plus-nat-closed (- n1 m1) <a> (- n2 m2) <b>))

    (have <d1> (= (+ (- n1 m1) (- n2 m2))
                  (- (+ (- n1 m1) n2) m2))
          :by (minus/assoc-plus-minus (- n1 m1) n2 m2))
    
    (have <d2> (= (+ (- n1 m1) (- n2 m2))
                  (- (+ n2 (- n1 m1)) m2))
          :by (eq/rewrite <d1> (plus/plus-commute (- n1 m1) n2)))
    
    (have <d3> (= (+ (- n1 m1) (- n2 m2))
                  (- (- (+ n2 n1) m1) m2))
          :by (eq/rewrite <d2> (minus/assoc-plus-minus n2 n1 m1)))

    (have <d4> (= (+ (- n1 m1) (- n2 m2))
                  (- (+ n2 n1) (+ m1 m2)))
          :by (eq/rewrite <d3> (minus/assoc-minus-plus-sym (+ n2 n1) m1 m2)))

    (have <d> (= (+ (- n1 m1) (- n2 m2))
                 (- (+ n1 n2) (+ m1 m2)))
          :by (eq/rewrite <d4> (plus/plus-commute n2 n1)))
    
    (have <e> (elem (- (+ n1 n2) (+ m1 m2)) nat)
          :by (eq/rewrite <c> <d>)))
  (qed <e>))

(definition >=
  "The greater-or-equal order for integers."
  [[n int] [m int]]
  (<= m n))

(definition >
  "The strict variant of [[>=]]."
  [[n int] [m int]]
  (< m n))

(defthm pos-gt-zero
  [[n int]]
  (==> (positive n)
       (> n zero)))

(proof 'pos-gt-zero
  (assume [Hpos (positive n)]
    (have <a1> (positive (succ n)) :by ((nat/positive-succ-strong n) Hpos))
    (have <a2> (elem n nat) :by ((nat/positive-succ-conv n) <a1>))
    (have <a3> (= n (- n zero)) :by (eq/eq-sym (minus/minus-zero n)))
    (have <a> (<= zero n) :by (eq/rewrite <a2> <a3>))
    (assume [Heq (= zero n)]
      (have <b1> (= n zero) :by (eq/eq-sym Heq))
      (have <b2> (positive zero)
            :by (eq/rewrite Hpos <b1>))
      (have <b> p/absurd :by (nat/nat-zero-has-no-pred <b2>)))
    (have <c> (> n zero) :by (p/and-intro <a> <b>)))
  (qed <c>))

(defthm pos-gt-zero-conv
  [[n int]]
  (==> (> n zero)
       (positive n)))

(proof 'pos-gt-zero-conv
  (assume [H (> n zero)]
    (have <a> (<= zero n) :by (p/and-elim-left H))
    (have <b> (not (= zero n)) :by (p/and-elim-right H))
    (have <c> (elem n nat)
          :by (eq/rewrite <a> (minus/minus-zero n)))
    "We proceed by nat-splitting."
    (assume [H1 (= n zero)]
      (have <d1> (= zero n) :by (eq/eq-sym H1))
      (have <d2> p/absurd :by (<b> <d1>))
      (have <d> (positive n) :by (<d2> (positive n))))
    (assume [H2 (positive n)]
      (have <e> (positive n) :by H2))
    (have <f> (or (= n zero) (positive n))
          :by (nat/nat-split n <c>))
    (have <g> (positive n)
          :by (p/or-elim <f> <d> <e>)))
  (qed <g>))

(defthm pos-gt-zero-equiv
  [[n int]]
  (<=> (positive n)
       (> n zero)))

(proof 'pos-gt-zero-equiv
  (qed (p/iff-intro (pos-gt-zero n)
                    (pos-gt-zero-conv n))))

(defthm nat-ge-zero
  [[n int]]
  (==> (elem n nat)
       (>= n zero)))

(proof 'nat-ge-zero
  (assume [Hn (elem n nat)]
    "We proceed by nat-splitting."
    (assume [Hz (= n zero)]
      (have <a1> (= (- n zero)
                    (- zero zero))
            :by (eq/eq-cong (lambda [j int] (- j zero))
                            Hz))
      (have <a2> (= (- n zero)
                    zero)
            :by (eq/rewrite <a1> (minus/minus-zero zero)))

      (have <a3> (= zero (- n zero))
            :by (eq/eq-sym <a2>))
      
      (have <a> (>= n zero)
            ;;(elem (- n zero) nat) 
            :by (eq/rewrite (nat/nat-zero) <a3>)))
    (assume [Hp (positive n)]
      (have <b1> (> n zero) :by ((pos-gt-zero n) Hp))
      (have <b> (>= n zero) :by (p/and-elim-left <b1>)))

    (have <c1> (or (= n zero) (positive n))
          :by (nat/nat-split n Hn))
    
    (have <c> (>= n zero) :by (p/or-elim <c1> <a> <b>)))
  (qed <c>))

(defthm neg-lt-zero
  [[n int]]
  (==> (negative n)
       (< n zero)))

(proof 'neg-lt-zero
  (assume [Hneg (negative n)]
    (have <a1> (= n (- n zero))
          :by (eq/eq-sym (minus/minus-zero n)))
    (have <a> (negative (- n zero))
          :by (eq/rewrite Hneg <a1>))
    (have <b> (positive (- zero n))
          :by ((minus/minus-pos-neg-conv zero n) <a>))
    (have <c> (positive (succ (- zero n)))
          :by ((nat/positive-succ-strong (- zero n)) <b>))
    (have <d> (<= n zero) :by ((nat/positive-succ-conv (- zero n))
                               <c>))
    (assume [Heq (= n zero)]
      (have <e1> (= zero n) :by (eq/eq-sym Heq))
      (have <e2> (elem n nat)
            :by (eq/rewrite (nat/nat-zero) <e1>))
      (have <e> p/absurd :by (Hneg <e2>)))
    (have <f> (< n zero) :by (p/and-intro <d> <e>)))
  (qed <f>))


(defthm neg-lt-zero-conv
  [[n int]]
  (==> (< n zero)
       (negative n)))

(proof 'neg-lt-zero-conv
  (assume [Hlt (< n zero)]
    (have <a> (<= n zero) :by (p/and-elim-left Hlt))
    (have <b> (not (= n zero)) :by (p/and-elim-right Hlt))
    (have <c> (elem (-- n) nat) :by (eq/rewrite <a> (eq/eq-sym (minus/opp-unfold n))))
    (have <d> (or (= n zero)
                  (negative n))
          :by ((minus/opp-nat-split n) <c>))
    "We proceed by case analysis."
    (assume [H1 (= n zero)]
      (have <e1> p/absurd :by (<b> H1))
      (have <e> (negative n) :by (<e1> (negative n))))
    (assume [H2 (negative n)]
      (have <f> (negative n) :by H2))
    (have <g> (negative n) :by (p/or-elim <d> <e> <f>)))
  (qed <g>))

(defthm neg-lt-zero-equiv
  [[n int]]
  (<=> (negative n)
       (< n zero)))

(proof 'neg-lt-zero-equiv
  (qed (p/iff-intro (neg-lt-zero n)
                    (neg-lt-zero-conv n))))

(defthm ord-int-split
  "Splitting an integer according to its (strict) ordering."
  [[n int]]
  (or (or (= n zero)
          (> n zero))
      (< n zero)))

(proof 'ord-int-split
  (assume [H1 (or (= n zero)
                  (positive n))]
    (assume [H2 (= n zero)]
      (have <a1> (= n zero) :by H2)
      (have <a> (or (= n zero)
                    (> n zero))
            :by (p/or-intro-left <a1> (> n zero))))
    (assume [H3 (positive n)]
      (have <b1> (> n zero) :by ((pos-gt-zero n) H3))
      (have <b> (or (= n zero)
                    (> n zero))
            :by (p/or-intro-right (= n zero) <b1>)))
    (have <c1> (or (= n zero)
                   (> n zero)) 
          :by (p/or-elim H1 <a> <b>))
    (have <c> (or (or (= n zero)
                      (> n zero))
                  (< n zero))
          :by (p/or-intro-left <c1> (< n zero))))
  (assume [H4 (negative n)]
    (have <d1> (< n zero) :by ((neg-lt-zero n) H4))
    (have <d> (or (or (= n zero)
                      (> n zero))
                  (< n zero))
          :by (p/or-intro-right (or (= n zero) (> n zero))
                                <d1>)))
  "We use int-splitting"
  (have <e> (or (or (= n zero) (> n zero))
                (< n zero)) 
        :by (p/or-elim (nat/int-split n) <c> <d>))
  (qed <e>))

(defthm lt-opp
  "Property about [[<]] wrt. [[--]]."
  [[n int] [m int]]
  (==> (< n m)
       (< (-- m) (-- n))))

(proof 'lt-opp
  (assume [Hlt (< n m)]
    (have <a> (<= n m) :by (p/and-elim-left Hlt))
    (have <b> (not (= n m)) :by (p/and-elim-right Hlt))
    (have <c> (<= (-- m) (-- n))
          :by (eq/rewrite <a> (minus/minus-opp m n)))
    (assume [Heq (= (-- m) (-- n))]
      (have <d1> (= m n) :by ((minus/minus-opp-cancel m n) Heq))
      (have <d2> (= n m) :by (eq/eq-sym <d1>))
      (have <d> p/absurd :by (<b> <d2>)))

    (have <e> (< (-- m) (-- n))
          :by (p/and-intro <c> <d>)))
  (qed <e>))

(defthm lt-opp-conv
  "The converse of [[lt-opp]]."
  [[n int] [m int]]
  (==> (< (-- m) (-- n))
       (< n m)))

(proof 'lt-opp-conv
  (assume [H (< (-- m) (-- n))]
    ;; (elem (- (-- n) (-- m)) int)))
    (have <a> (elem (- (-- n) (-- m)) nat)
          :by (p/and-elim-left H))
    (have <b> (not (= (-- m) (-- n)))
          :by (p/and-elim-right H))
    (have <c> (= (- (-- n) (-- m))
                 (- m n))
          :by (eq/eq-sym (minus/minus-opp m n)))
    (have <d> (<= n m)
          :by (eq/rewrite <a> <c>))
    (assume [Heq (= n m)]
      (have <e1> (= (-- m) (-- n))
            :by (eq/rewrite (eq/eq-refl (-- n)) Heq))
      (have <e> p/absurd :by (<b> <e1>)))
    (have <f> _ :by (p/and-intro <d> <e>)))
  (qed <f>))


(defthm lt-opp-equiv
  "Property about [[<]] wrt. [[--]]."
  [[n int] [m int]]
  (<=> (< n m)
       (< (-- m) (-- n))))

(proof 'lt-opp-equiv
  (qed (p/iff-intro (lt-opp n m)
                    (lt-opp-conv n m))))

(defthm lt-zero-opp
  [[n int]]
  (==> (< n zero)
       (> (-- n) zero)))

(proof 'lt-zero-opp
  (assume [H (< n zero)]
    [:transparent '--]
    (have <a> (elem (-- n) nat)
          :by (p/and-elim-left H))
    [:opaque '--]
    (have <b> (not (= n zero))
          :by (p/and-elim-right H))
    (have <c> (or (= n zero)
                  (negative n))
          :by ((minus/opp-nat-split n) <a>))
    "We proceed by case analysis"
    (assume [H1 (= n zero)]
      (have <d1> p/absurd :by (<b> H1))
      (have <d> (> (-- n) zero) :by (<d1> (> (-- n) zero))))

    (assume [H2 (negative n)]
      (have <e1> (= (-- n)
                    (- (-- n) zero))
            :by (eq/eq-sym (minus/minus-zero (-- n))))
      (have <e> (<= zero (-- n))
            :by (eq/rewrite <a> <e1>))
      (assume [Heq (= zero (-- n))]
        (have <f1> (= (-- n) zero)
              :by (eq/eq-sym Heq))
        (have <f2> (= n zero)
              :by ((minus/zero-opp-zero-conv n) <f1>))
        (have <f> p/absurd :by (<b> <f2>)))
      
      (have <g> (> (-- n) zero)
            :by (p/and-intro <e> <f>)))
    
    (have <h> (> (-- n) zero) :by (p/or-elim <c> <d> <g>)))
  (qed <h>))

(defthm lt-zero-opp-conv
  [[n int]]
  (==> (> (-- n) zero)
       (< n zero)))

(proof 'lt-zero-opp-conv
  (assume [H (> (-- n) zero)]
    (have <a> (<= zero (-- n))  ;; (elem (- (-- n) zero) nat)
          :by (p/and-elim-left H))
    (have <b> (not (= zero (-- n)))
          :by (p/and-elim-right H))
    (have <c> (elem (-- n) nat)
          :by (eq/rewrite <a> (minus/minus-zero (-- n))))
    (have <d> (or (= n zero)
                  (negative n))
          :by ((minus/opp-nat-split n) <c>))
    "We proceed by case analysis."
    (assume [H1 (= n zero)]
      (have <e1> (= (-- n) zero) :by ((minus/zero-opp-zero n) H1))
      (have <e2> (= zero (-- n)) :by (eq/eq-sym <e1>))
      (have <e3> p/absurd :by (<b> <e2>))
      (have <e> (< n zero) :by (<e3> (< n zero))))
    (assume [H2 (negative n)]
      (have <f> (< n zero) :by ((neg-lt-zero n) H2)))
    (have <g> (< n zero) :by (p/or-elim <d> <e> <f>)))
  (qed <g>))

(defthm lt-zero-opp-equiv
  [[n int]]
  (<=> (< n zero)
       (> (-- n) zero)))

(proof 'lt-zero-opp-equiv
  (qed (p/iff-intro (lt-zero-opp n)
                    (lt-zero-opp-conv n))))

(defthm minus-lt
  [[m int] [n int] [p int]]
  (==> (< (- m p) (- n p))
       (< m n)))

(proof 'minus-lt
  (assume [H (< (- m p) (- n p))]
    (have <a> (= (+ (- m p) p) m)
          :by (minus/minus-prop m p))
    (have <b> (= (+ (- n p) p) n)
          :by (minus/minus-prop n p))
    (have <c> (< (+ (- m p) p) (+ (- n p) p))
          :by ((plus-lt-conv (- m p) (- n p) p) H))
    (have <d> (< m (+ (- n p) p))
          :by (eq/rewrite <c> <a>))
    (have <e> (< m n)
          :by (eq/rewrite <d> <b>)))
  (qed <e>))

(defthm minus-lt-conv
  [[m int] [n int] [p int]]
  (==> (< m n)
       (< (- m p) (- n p))))

(proof 'minus-lt-conv
  (assume [Hmn (< m n)]
    (have <a> (= (+ m (-- p)) (- m p))
          :by (minus/plus-opp-minus m p))
    (have <b> (= (+ n (-- p)) (- n p))
          :by (minus/plus-opp-minus n p))
    (have <c> (< (+ m (-- p)) (+ n (-- p)))
          :by ((plus-lt-conv m n (-- p)) Hmn))
    (have <d> (< (- m p) (+ n (-- p)))
          :by (eq/rewrite <c> <a>))
    (have <e> (< (- m p) (- n p))
          :by (eq/rewrite <d> <b>)))
  (qed <e>))

(defthm lt-succ
  "Strict ordering of successors."
  [[n int]]
  (< n (succ n)))

(proof 'lt-succ
  (have <a> (= (- (succ n) n)
               (succ (- n n)))
        :by (minus/minus-succ n n))
  (have <b> (= (succ (- n n))
               (succ zero))
        :by (eq/eq-cong succ (minus/minus-cancel n)))
  (have <c1> (= (- (succ n) n)
               (succ zero))
        :by (eq/eq-trans <a> <b>))
  (have <c> (= (succ zero)
               (- (succ n) n)) :by (eq/eq-sym <c1>))
  (have <d> (elem (succ zero) nat)
        :by ((nat/nat-succ zero) nat/nat-zero))
  (have <e> (<= n (succ n)) ;;(elem (- (succ n) n) nat)
        :by (eq/rewrite <d> <c>))
  (assume [Heq (= n (succ n))]
    (have <f1> (= (- n n) (- (succ n) n))
          :by (eq/eq-cong (lambda [k int] (- k n))
                          Heq))
    (have <f2> (= zero (- (succ n) n))
          :by (eq/rewrite <f1> (minus/minus-cancel n)))
    (have <f3> (= zero (succ zero))
          :by (eq/rewrite <f2> <c1>))
    (have <f4> (= (succ zero) zero)
          :by (eq/eq-sym <f3>))
    (have <f5> (not (= (succ zero) zero))
          :by ((nat/nat-zero-is-not-succ zero) nat/nat-zero))
    (have <f> p/absurd :by (<f5> <f4>)))

  (have <g> (< n (succ n)) :by (p/and-intro <e> <f>))

  (qed <g>))


(defthm lt-succ-cong
  [[m int] [n int]]
  (==> (< m n)
       (< (succ m) (succ n))))


(proof 'lt-succ-cong
  (assume [Hmn (< m n)]
    (have <a> (= (+ m one) (succ m))
          :by (plus/plus-one m))
    (have <b> (= (+ n one) (succ n))
          :by (plus/plus-one n))
    (have <c> (< (+ m one) (+ n one))
          :by ((plus-lt-conv m n one) Hmn))
    ;; XXX : there's an issue with normalization here...
    [:opaque '<]
    (have <d> (< (succ m) (+ n one))
          :by (eq/rewrite <c> <a>))
    (have <e> (< (succ m) (succ n))
          :by (eq/rewrite <d> <b>)))
  [:transparent '<]
  (qed <e>))

(defthm lt-pred
  [[m int]]
  (< (pred m) m))

(proof 'lt-pred
  (have <a> (< m (succ m))
        :by (lt-succ m))
  (have <b> (< (- m one) (- (succ m) one))
        :by ((minus-lt-conv m (succ m) one) <a>))
  (have <c> (= (- m one) (pred m))
        :by (minus/minus-one m))
  (have <d1> (= (- (succ m) one) (pred (succ m)))
        :by (minus/minus-one (succ m)))
  (have <d> (= (- (succ m) one) m)
        :by (eq/rewrite <d1> (int/pred-of-succ m))) 
  ;;; XXX : still probably a normalization bug (or a problem with the rewrite proof method ?)
  [:opaque '<]
  (have <e> (< (pred m) (- (succ m) one))
        :by (eq/rewrite <b> <c>)) 
  (have <f> (< (pred m) m)
        :by (eq/rewrite <e> <d>))

  [:transparent '<]
  (qed <f>))

(defthm lt-pred-cong
  [[m int] [n int]]
  (==> (< m n)
       (< (pred m) (pred n))))

(proof 'lt-pred-cong
  (assume [Hmn (< m n)]
    (have <a> (= (- m one) (pred m))
          :by (minus/minus-one m))
    (have <b> (= (- n one) (pred n))
          :by (minus/minus-one n))
    (have <c> (< (- m one) (- n one))
          :by ((minus-lt-conv m n one) Hmn))
    ;;; XXX : still the same problem
    [:opaque '<]
    (have <d> (< (pred m) (- n one))
          :by (eq/rewrite <c> <a>))
    (have <e> (< (pred m) (pred n))
          :by (eq/rewrite <d> <b>)))
  [:transparent '<]
  (qed <e>))

(defthm lt-pred-cong-conv
  [[m int] [n int]]
  (==> (< (pred m) (pred n))
       (< m n)))

(proof 'lt-pred-cong-conv
  (assume [Hmn (< (pred m) (pred n))]
    (have <a> (< (succ (pred m)) (succ (pred n)))
          :by ((lt-succ-cong (pred m) (pred n)) Hmn))
    (have <b> (< m (succ (pred n)))
          :by (eq/rewrite <a> (int/succ-of-pred m)))
    (have <c> (< m n)
          :by (eq/rewrite <b> (int/succ-of-pred n))))
  (qed <c>))


(defthm lt-succ-cong-conv
  [[m int] [n int]]
  (==> (< (succ m) (succ n))
       (< m n)))

(proof 'lt-succ-cong-conv
  (assume [Hmn (< (succ m) (succ n))]
    (have <a> (< (pred (succ m)) (pred (succ n)))
          :by ((lt-pred-cong (succ m) (succ n)) Hmn))
    (have <b> (< m (pred (succ n)))
          :by (eq/rewrite <a> (int/pred-of-succ m)))
    (have <c> (< m n)
          :by (eq/rewrite <b> (int/pred-of-succ n))))
  (qed <c>))

(defthm lt-succ-weak
  [[m int] [n int]]
  (==> (< m (succ n))
       (<= m n)))

(proof 'lt-succ-weak
  (assume [Hmn (< m (succ n))]
    (have <a> (elem (- (succ n) m) nat)
          :by (p/and-elim-left Hmn))
    (have <b> (elem (succ (- n m)) nat)
          :by (eq/rewrite <a> (minus/minus-succ n m)))
    "We use the nat-split principle."
    (have <c> (or (= (succ (- n m)) zero)
                  (positive (succ (- n m))))
          :by (nat/nat-split (succ (- n m)) <b>))
    (assume [Hzero (= (succ (- n m)) zero)]
      (have <d1> (= (succ (- n m)) (- (succ n) m))
            :by (eq/eq-sym (minus/minus-succ n m)))
      (have <d2> (= (- (succ n) m) zero)
            :by (eq/rewrite Hzero <d1>))
      (have <d3> (= m (succ n))
            :by (eq/eq-sym ((minus/minus-zero-alt (succ n) m) <d2>)))
      (have <d4> (not (= m (succ n)))
            :by (p/and-elim-right Hmn))
      (have <d5> p/absurd :by (<d4> <d3>))
      (have <d> (<= m n) :by (<d5> (<= m n))))
    (assume [Hpos (positive (succ (- n m)))]
      (have <e> (<= m n)
            :by (eq/rewrite Hpos (int/pred-of-succ (- n m)))))
    "We apply the split rule."
    (have <f> (<= m n) :by (p/or-elim <c> <d> <e>)))
  (qed <f>))


(defthm pos-ge-one
  [[n int]]
  (==> (positive n)
       (>= n one)))

(proof 'pos-ge-one
  (assume [Hpos (positive n)]
    (have <a> (> n zero) :by ((pos-gt-zero n) Hpos))
    (have <b> (> (succ n) one)
          :by ((lt-succ-cong zero n) <a>))
    (have <c> (>= n one)
          :by ((lt-succ-weak one n) <b>)))
  (qed <c>))

(defthm pos-one-split
  "A split princple for positive numbers wrt. [[int/one]]."
  [[n int]]
  (==> (positive n)
       (or (= n one)
           (> n one))))

(proof 'pos-one-split
  (assume [Hn (positive n)]
    (have <a> (>= n one) :by ((pos-ge-one n) Hn))
    (have <b> (or (= one n)
                  (> n one))
          :by ((le-lt-split one n) <a>))
    (assume [H1 (= one n)]
      (have <c1> (= n one) :by (eq/eq-sym H1))
      (have <c> _ :by (p/or-intro-left <c1> (> n one))))
    (assume [H2 (> n one)]
      (have <d> _ :by (p/or-intro-right (= n one) H2)))
    (have <e> (or (= n one)
                  (> n one))
          :by (p/or-elim <b> <c> <d>)))
  (qed <e>))


;;(u/set-opacity! #'> true)
;;(u/set-opacity! #'>= true)
;;(u/set-opacity! #'< true)
(u/set-opacity! #'<= true)

