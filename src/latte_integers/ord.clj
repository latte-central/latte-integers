(ns latte-integers.ord

  "The natural ordering on integers."

  (:refer-clojure :exclude [and or not int = + - < <= > >=])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          try-proof ==>]]

            [latte.prop :as p :refer [and or not <=>]]
            [latte.equal :as eq :refer [equal]]
            [latte.quant :as q :refer [exists]]
            [latte.fun :as fun]

            [latte-sets.core :as set :refer [elem forall-in]]

            [latte-integers.core :as int :refer [zero one succ pred int =]]
            [latte-integers.nat :as nat :refer [nat positive negative]]
            [latte-integers.rec :as rec]
            [latte-integers.plus :as plus :refer [+]]
            [latte-integers.minus :as minus :refer [- --]]))

(definition <=
  "The lower-or-equal order for integers."
  [[n int] [m int]]
  (elem int (- m n) nat))

(defthm le-refl
  [[n int]]
  (<= n n))

(proof le-refl
    :script
  (have <a> (= zero (- n n))
        :by (eq/eq-sym% (minus/minus-cancel n)))
  (have <b> (<= n n)
        :by (eq/eq-subst% (lambda [k int] (elem int k nat))
                          <a>
                          (nat/nat-zero)))
  (qed <b>))

(defthm le-trans
  [[n int] [m int] [p int]]
  (==> (<= n m)
       (<= m p)
       (<= n p)))

(proof le-trans
    :script
  (assume [Hnm (<= n m)
           Hmp (<= m p)]

    (have <a> (elem int (+ (- m n) (- p m)) nat)
          :by (plus/plus-nat-closed (- m n) Hnm
                                    (- p m) Hmp))

    (have <b> (elem int (+ (- p m) (- m n)) nat)
          :by (eq/eq-subst% (lambda [k int] (elem int k nat))
                            (plus/plus-commute (- m n) (- p m))
                            <a>))

    (have <c> (elem int (- (+ (- p m) m) n) nat)
          :by (eq/eq-subst% (lambda [k int] (elem int k nat))
                            (minus/assoc-plus-minus (- p m) m n)
                            <b>))

    (have <d> (<= n p)
          :by (eq/eq-subst% (lambda [k int] (elem int (- k n) nat))
                            (minus/minus-prop p m)
                            (<c>)))

    (qed <d>)))

(defthm le-antisym
  [[n int] [m int]]
  (==> (<= n m)
       (<= m n)
       (= n m)))

(proof le-antisym
    :script
  (assume [Hnm (<= n m)  ;; (elem int (- m n) nat)
           Hmn (<= m n)] ;; (elem int (- n m) nat)

    ;; (or (= (- m n) zero) (positive (- m n)))
    (assume [H1 (= (- m n) zero)]
      (have <a1> (= (+ (- m n) n)
                    (+ zero n))
            :by (eq/eq-cong% (lambda [k int] (+ k n))
                             H1))
      (have <a2> (= m (+ zero n))
            :by (eq/eq-subst% (lambda [k int] (= k (+ zero n)))
                              (minus/minus-prop m n)
                              <a1>))
      (have <a3> (= m n)
            :by (eq/eq-subst% (lambda [k int] (= m k))
                              (plus/plus-zero-swap n)
                              <a2>))
      (have <a> (= n m) :by (eq/eq-sym% <a3>)))
    (assume [H2 (positive (- m n))]
      (have <b1> (negative (- n m))
            :by ((minus/minus-pos-neg m n) H2))
      (have <b2> p/absurd :by (<b1> Hmn))
      (have <b> (= n m) :by (<b2> (= n m))))
    "We use the nat splitting principle."
    (have <c> (or (= (- m n) zero)
                  (positive (- m n)))
          :by (nat/nat-split (- m n) Hnm))
    (have <d> _
          :by (p/or-elim% <c>
                          (= n m)
                          <a> <b>))

    (qed <d>)))

(definition <
  "The strict variant of [[<=]]."
  [[n int] [m int]]
  (and (<= n m)
       (not (= n m))))

;; (defthm lt-trans-weak-fst
;;   [[n int] [m int] [p int]]
;;   (==> (<= n m)
;;        (< m p)
;;        (< n p)))

;; (defthm lt-trans-weak-snd
;;   [[n int] [m int] [p int]]
;;   (==> (< n m)
;;        (<= m p)
;;        (< n p)))


(defthm lt-asym
  [[n int] [m int]]
  (==> (< n m)
       (not (< m n))))

(proof lt-asym
    :script
  (assume [Hnm (< n m)]
    (assume [Hmn (< m n)]
      (have <a> (= n m)
            :by ((le-antisym n m)
                 (p/and-elim-left% Hnm)
                 (p/and-elim-left% Hmn)))
      (have <b> p/absurd :by ((p/and-elim-right% Hnm) <a>)))
    (qed <b>)))

(defthm lt-trans
  [[n int] [m int] [p int]]
  (==> (< n m)
       (< m p)
       (< n p)))

(proof lt-trans
    :script
  (assume [Hnm (< n m)
           Hmp (< m p)]
    (have <a> (<= n m) :by (p/and-elim-left% Hnm))
    (have <b> (not (= n m)) :by (p/and-elim-right% Hnm))
    (have <c> (<= m p) :by (p/and-elim-left% Hmp))
    (have <d> (not (= m p)) :by (p/and-elim-right% Hmp))
    (have <e> (<= n p) :by ((le-trans n m p) <a> <c>))
    (assume [Hcut (= n p)]
      (have <f1> (< p m)
            :by (eq/eq-subst% (lambda [k int] (< k m))
                              Hcut
                              Hnm))
      (have <f2> (not (< p m)) :by ((lt-asym m p) Hmp))
      (have <f> p/absurd :by (<f2> <f1>)))
    (have <g> (< n p)
          :by (p/and-intro% <e> <f>))
    (qed <g>)))

(defthm lt-trans-weak
  [[n int] [m int] [p int]]
  (==> (<= n m)
       (< m p)
       (< n p)))

(proof lt-trans-weak
    :script
  (assume [Hnm (<= n m)
           Hmp (< m p)]
    (have <a> (<= m p) :by (p/and-elim-left% Hmp))
    (have <b> (not (= m p)) :by (p/and-elim-right% Hmp))
    (have <c> (<= n p) :by ((le-trans n m p) Hnm <a>))
    (assume [H (= n p)]
      (have <d1> (<= p m) :by (eq/eq-subst% (lambda [k int] (<= k m))
                                            H Hnm))
      (have <d2> (= m p) :by ((le-antisym m p) <a> <d1>))
      (have <d> p/absurd :by (<b> <d2>)))
    (have <e> (< n p) :by (p/and-intro% <c> <d>))
    (qed <e>)))

(defthm lt-trans-weak-alt
  "An alternative to [[lt-trans-weak]]."
  [[n int] [m int] [p int]]
  (==> (< n m)
       (<= m p)
       (< n p)))

(proof lt-trans-weak-alt
    :script
  (assume [Hnm (< n m)
           Hmp (<= m p)]
    (have <a> (<= n m) :by (p/and-elim-left% Hnm))
    (have <b> (not (= n m)) :by (p/and-elim-right% Hnm))
    (have <c> (<= n p) :by ((le-trans n m p) <a> Hmp))
    (assume [H (= n p)]
      (have <d1> (= p n) :by (eq/eq-sym% H))
      (have <d2> (<= m n) :by (eq/eq-subst% (lambda [k int] (<= m k))
                                            <d1> Hmp))
      (have <d3> (= n m) :by ((le-antisym n m) <a> <d2>))
      (have <d> p/absurd :by (<b> <d3>)))
    (have <e> (< n p) :by (p/and-intro% <c> <d>))
    (qed <e>)))


(defthm plus-le
  [[n int] [m int] [p int]]
  (==> (<= (+ n p) (+ m p))
       (<= n m)))

(proof plus-le
    :script
  (assume [H (<= (+ n p) (+ m p))]
    (have <a> (elem int (- (+ m p) (+ p n)) nat)
          :by (eq/eq-subst% (lambda [k int] (elem int (- (+ m p) k) nat))
                            (plus/plus-commute n p)
                            H))
    (have <b> (elem int (- (- (+ m p) p) n) nat)
          :by (eq/eq-subst% (lambda [k int] (elem int k nat))
                            (minus/assoc-minus-plus (+ m p) p n)
                            <a>))
    (have <c> (<= n m)
          :by (eq/eq-subst% (lambda [k int] (elem int (- k n) nat))
                            (minus/minus-prop-cons m p)
                            <b>))
    (qed <c>)))


(defthm plus-le-conv
  "The converse of [[plus-le]]."
  [[n int] [m int] [p int]]
  (==> (<= n m)
       (<= (+ n p) (+ m p))))

(proof plus-le-conv
    :script
  (assume [H (<= n m)]

    (have <a1> (= (- m n) (+ (- m n) zero))
          :by (eq/eq-sym% (plus/plus-zero (- m n))))
    (have <a2> (= zero (- p p))
          :by (eq/eq-sym% (minus/minus-cancel p)))
    (have <a3> (= (- m n) (+ (- m n) (- p p)))
          :by (eq/eq-subst% (lambda [k int] (= (- m n) (+ (- m n) k)))
                            <a2>
                            <a1>))
    (have <a> (elem int (+ (- m n) (- p p)) nat)
          :by (eq/eq-subst% (lambda [k int] (elem int k nat))
                            <a3>
                            H))

    (have <b> (elem int (- (+ (- m n) p) p) nat)
          :by (eq/eq-subst% (lambda [k int] (elem int k nat))
                            (minus/assoc-plus-minus (- m n) p p)
                            <a>))

    (have <c> (elem int (- (+ p (- m n)) p) nat)
          :by (eq/eq-subst% (lambda [k int] (elem int (- k p) nat))
                            (plus/plus-commute (- m n) p)
                            <b>))

    (have <d> (elem int (- (- (+ p m) n) p) nat)
          :by (eq/eq-subst% (lambda [k int] (elem int (- k p) nat))
                            (minus/assoc-plus-minus p m n)
                            <c>))

    (have <e> (= (- (- (+ p m) n) p)
                 (- (+ p m) (+ n p)))
          :by (eq/eq-sym% (minus/assoc-minus-plus (+ p m) n p)))

    (have <f> (= (- (- (+ p m) n) p)
                 (- (+ m p) (+ n p)))
          :by (eq/eq-subst% (lambda [k int] (= (- (- (+ p m) n) p)
                                               (- k (+ n p))))
                            (plus/plus-commute p m)
                            <e>))

    (have <g> (elem int (- (+ m p) (+ n p)) nat)
          :by (eq/eq-subst% (lambda [k int] (elem int k nat))
                            <f>
                            <d>))

    (qed <g>)))

(defthm plus-le-equiv
  [[n int] [m int] [p int]]
  (<=> (<= (+ n p) (+ m p))
       (<= n m)))

(proof plus-le-equiv
    :script
  (have <a> _ :by (p/and-intro% (plus-le n m p)
                                (plus-le-conv n m p)))
  (qed <a>))


(defthm plus-lt
  [[n int] [m int] [p int]]
  (==> (< (+ n p) (+ m p))
       (< n m)))

(proof plus-lt
    :script
  (assume [H (< (+ n p) (+ m p))]
    (have <a> (<= (+ n p) (+ m p))
          :by (p/and-elim-left% H))
    (have <b> (not (= (+ n p) (+ m p)))
          :by (p/and-elim-right% H))
    (have <c> (<= n m)
          :by ((plus-le n m p) <a>))
    (assume [H2 (= n m)]
      (have <d1> (= (+ n p) (+ m p))
            :by ((plus/plus-right-cancel-conv n m p) H2))
      (have <d> p/absurd :by (<b> <d1>)))
    (have <e> (< n m)
          :by (p/and-intro% <c> <d>))
      (qed <e>)))

(defthm plus-lt-conv
  [[n int] [m int] [p int]]
  (==> (< n m)
       (< (+ n p) (+ m p))))

(proof plus-lt-conv
    :script
  (assume [H (< n m)]
    (have <a> (<= n m) :by (p/and-elim-left% H))
    (have <b> (not (= n m)) :by (p/and-elim-right% H))
    (have <c> (<= (+ n p) (+ m p))
          :by ((plus-le-conv n m p) <a>))
    (assume [H2 (= (+ n p) (+ m p))]
      (have <d1> (= n m) :by ((plus/plus-right-cancel n m p) H2))
      (have <d> p/absurd :by (<b> <d1>)))
    (have <e> (< (+ n p) (+ m p))
          :by (p/and-intro% <c> <d>))
    (qed <e>)))

(defthm plus-lt-equiv
  [[n int] [m int] [p int]]
  (<=> (< (+ n p) (+ m p))
       (< n m)))

(proof plus-lt-equiv
    :script
  (have <a> _ :by (p/and-intro% (plus-lt n m p)
                                (plus-lt-conv n m p)))
  (qed <a>))

(defthm plus-le-cong
  [[m1 int] [m2 int] [n1 int] [n2 int]]
  (==> (<= m1 n1)
       (<= m2 n2)
       (<= (+ m1 m2) (+ n1 n2))))

(proof plus-le-cong
    :script
  (assume [H1 (<= m1 n1)
           H2 (<= m2 n2)]
    (have <a> (elem int (- n1 m1) nat) :by H1)
    (have <b> (elem int (- n2 m2) nat) :by H2)
    (have <c> (elem int (+ (- n1 m1) (- n2 m2)) nat)
          :by (plus/plus-nat-closed (- n1 m1) <a> (- n2 m2) <b>))

    (have <d1> (= (+ (- n1 m1) (- n2 m2))
                  (- (+ (- n1 m1) n2) m2))
          :by (minus/assoc-plus-minus (- n1 m1) n2 m2))
    
    (have <d2> (= (+ (- n1 m1) (- n2 m2))
                  (- (+ n2 (- n1 m1)) m2))
          :by (eq/eq-subst% (lambda [k int]
                              (= (+ (- n1 m1) (- n2 m2))
                                 (- k m2)))
                            (plus/plus-commute (- n1 m1) n2)
                            <d1>))
    
    (have <d3> (= (+ (- n1 m1) (- n2 m2))
                  (- (- (+ n2 n1) m1) m2))
          :by (eq/eq-subst% (lambda [k int]
                              (= (+ (- n1 m1) (- n2 m2))
                                 (- k m2)))
                            (minus/assoc-plus-minus n2 n1 m1)
                            <d2>))

    (have <d4> (= (+ (- n1 m1) (- n2 m2))
                  (- (+ n2 n1) (+ m1 m2)))
          :by (eq/eq-subst% (lambda [k int]
                              (= (+ (- n1 m1) (- n2 m2))
                                 k))
                            (minus/assoc-minus-plus-sym (+ n2 n1) m1 m2)
                            <d3>))

    (have <d> (= (+ (- n1 m1) (- n2 m2))
                 (- (+ n1 n2) (+ m1 m2)))
          :by (eq/eq-subst% (lambda [k int]
                              (= (+ (- n1 m1) (- n2 m2))
                                 (- k (+ m1 m2))))
                            (plus/plus-commute n2 n1)
                            <d4>))

    (have <e> (elem int (- (+ n1 n2) (+ m1 m2)) nat)
          :by (eq/eq-subst% (lambda [k int] (elem int k nat))
                            <d> <c>))
    (qed <e>)))

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

(proof pos-gt-zero
    :script
  (assume [Hpos (positive n)]
    (have <a1> (positive (succ n)) :by ((nat/positive-succ-strong n) Hpos))
    (have <a2> (elem int n nat) :by ((nat/positive-succ-conv n) <a1>))
    (have <a3> (= n (- n zero)) :by (eq/eq-sym% (minus/minus-zero n)))
    (have <a> (<= zero n) :by (eq/eq-subst% (lambda [k int] (elem int k nat))
                                            <a3> <a2>))
    (assume [Heq (= zero n)]
      (have <b1> (= n zero) :by (eq/eq-sym% Heq))
      (have <b2> (positive zero)
            :by (eq/eq-subst% positive <b1> Hpos))
      (have <b> p/absurd :by (nat/nat-zero-has-no-pred <b2>)))
    (have <c> (> n zero) :by (p/and-intro% <a> <b>))
    (qed <c>)))

(defthm pos-gt-zero-conv
  [[n int]]
  (==> (> n zero)
       (positive n)))

(proof pos-gt-zero-conv
    :script
  (assume [H (> n zero)]
    (have <a> (<= zero n) :by (p/and-elim-left% H))
    (have <b> (not (= zero n)) :by (p/and-elim-right% H))
    (have <c> (elem int n nat)
          :by (eq/eq-subst% (lambda [k int] (elem int k nat))
                            (minus/minus-zero n)
                            <a>))
    "We proceed by nat-splitting."
    (assume [H1 (= n zero)]
      (have <d1> (= zero n) :by (eq/eq-sym% H1))
      (have <d2> p/absurd :by (<b> <d1>))
      (have <d> (positive n) :by (<d2> (positive n))))
    (assume [H2 (positive n)]
      (have <e> (positive n) :by H2))
    (have <f> (or (= n zero) (positive n))
          :by (nat/nat-split n <c>))
    (have <g> (positive n)
          :by (p/or-elim% <f> (positive n) <d> <e>)) ; XXX: decompose-or-type issue here
                                                     ; if we perform <f> directly (tofix...)
    (qed <g>)))

(defthm pos-gt-zero-equiv
  [[n int]]
  (<=> (positive n)
       (> n zero)))

(proof pos-gt-zero-equiv
    :script
  (have <a> _ :by (p/and-intro% (pos-gt-zero n)
                                (pos-gt-zero-conv n)))
  (qed <a>))

(defthm nat-ge-zero
  [[n int]]
  (==> (elem int n nat)
       (>= n zero)))

(proof nat-ge-zero
    :script
  (assume [Hn (elem int n nat)]
    "We proceed by nat-splitting."
    (assume [Hz (= n zero)]
      (have <a1> (= (- n zero)
                    (- zero zero))
            :by (eq/eq-cong% (lambda [j int] (- j zero))
                             Hz))
      (have <a2> (= (- n zero)
                    zero)
            :by (eq/eq-subst% (lambda [j int]
                                (= (- n zero)
                                   j))
                              (minus/minus-zero zero)
                              <a1>))

      (have <a3> (= zero (- n zero))
            :by (eq/eq-sym% <a2>))
      
      (have <a> (>= n zero)
            ;;(elem int (- n zero) nat) 
            :by (eq/eq-subst% (lambda [j int]
                                (elem int j nat))
                              <a3>
                              (nat/nat-zero))))
    (assume [Hp (positive n)]
      (have <b1> (> n zero) :by ((pos-gt-zero n) Hp))
      (have <b> (>= n zero) :by (p/and-elim-left% <b1>)))

    (have <c1> (or (= n zero) (positive n))
          :by (nat/nat-split n Hn))
    
    (have <c> _ :by (p/or-elim% <c1>
                                (>= n zero)
                                <a> <b>))
    (qed <c>)))

(defthm neg-lt-zero
  [[n int]]
  (==> (negative n)
       (< n zero)))

(proof neg-lt-zero
    :script
  (assume [Hneg (negative n)]
    (have <a1> (= n (- n zero))
          :by (eq/eq-sym% (minus/minus-zero n)))
    (have <a> (negative (- n zero))
          :by (eq/eq-subst% negative
                            <a1>
                            Hneg))
    (have <b> (positive (- zero n))
          :by ((minus/minus-pos-neg-conv zero n) <a>))
    (have <c> (positive (succ (- zero n)))
          :by ((nat/positive-succ-strong (- zero n)) <b>))
    (have <d> (<= n zero) :by ((nat/positive-succ-conv (- zero n))
                               <c>))
    (assume [Heq (= n zero)]
      (have <e1> (= zero n) :by (eq/eq-sym% Heq))
      (have <e2> (elem int n nat)
            :by (eq/eq-subst% (lambda [k int] (elem int k nat))
                              <e1> (nat/nat-zero)))
      (have <e> p/absurd :by (Hneg <e2>)))
    (have <f> (< n zero) :by (p/and-intro% <d> <e>))
    (qed <f>)))


(defthm neg-lt-zero-conv
  [[n int]]
  (==> (< n zero)
       (negative n)))

(proof neg-lt-zero-conv
    :script
  (assume [Hlt (< n zero)]
    (have <a> (<= n zero) :by (p/and-elim-left% Hlt))
    (have <b> (not (= n zero)) :by (p/and-elim-right% Hlt))
    (have <c> (elem int (-- n) nat) :by <a>)
    (have <d> (or (= n zero)
                  (negative n))
          :by ((minus/opp-nat-split n) <c>))
    "We proceed by case analysis."
    (assume [H1 (= n zero)]
      (have <e1> p/absurd :by (<b> H1))
      (have <e> (negative n) :by (<e1> (negative n))))
    (assume [H2 (negative n)]
      (have <f> (negative n) :by H2))
    (have <g> (negative n) :by (p/or-elim% <d> (negative n)
                                           <e> <f>))
    (qed <g>)))

(defthm neg-lt-zero-equiv
  [[n int]]
  (<=> (negative n)
       (< n zero)))

(proof neg-lt-zero-equiv
    :script
  (have <a> _ :by (p/and-intro% (neg-lt-zero n)
                                (neg-lt-zero-conv n)))
  (qed <a>))

(defthm ord-int-split
  "Splitting an integer according to its (strict) ordering."
  [[n int]]
  (or (or (= n zero)
          (> n zero))
      (< n zero)))

(proof ord-int-split
    :script
  (assume [H1 (or (= n zero)
                  (positive n))]
    (assume [H2 (= n zero)]
      (have <a1> (= n zero) :by H2)
      (have <a> (or (= n zero)
                    (> n zero))
            :by (p/or-intro-left% <a1> (> n zero))))
    (assume [H3 (positive n)]
      (have <b1> (> n zero) :by ((pos-gt-zero n) H3))
      (have <b> (or (= n zero)
                    (> n zero))
            :by (p/or-intro-right% (= n zero) <b1>)))
    (have <c1> _ :by (p/or-elim% H1 (or (= n zero)
                                        (> n zero)) <a> <b>))
    (have <c> (or (or (= n zero)
                      (> n zero))
                  (< n zero))
          :by (p/or-intro-left% <c1> (< n zero))))
  (assume [H4 (negative n)]
    (have <d1> (< n zero) :by ((neg-lt-zero n) H4))
    (have <d> (or (or (= n zero)
                      (> n zero))
                  (< n zero))
          :by (p/or-intro-right% (or (= n zero) (> n zero))
                                 <d1>)))
  "We use int-splitting"
  (have <e> _ :by (p/or-elim% (nat/int-split n)
                              (or (or (= n zero) (> n zero))
                                  (< n zero))
                              <c> <d>))
  (qed <e>))

(defthm lt-opp
  "Property about [[<]] wrt. [[--]]."
  [[n int] [m int]]
  (==> (< n m)
       (< (-- m) (-- n))))

(proof lt-opp
    :script
  (assume [Hlt (< n m)]
    (have <a> (<= n m) :by (p/and-elim-left% Hlt))
    (have <b> (not (= n m)) :by (p/and-elim-right% Hlt))
    (have <c> (<= (-- m) (-- n))
          :by (eq/eq-subst% (lambda [k int] (elem int k nat))
                            (minus/minus-opp m n)
                            <a>))
    (assume [Heq (= (-- m) (-- n))]
      (have <d1> (= m n) :by ((minus/minus-opp-cancel m n) Heq))
      (have <d2> (= n m) :by (eq/eq-sym% <d1>))
      (have <d> p/absurd :by (<b> <d2>)))

    (have <e> (< (-- m) (-- n))
          :by (p/and-intro% <c> <d>))
    (qed <e>)))


(defthm lt-opp-conv
  "The converse of [[lt-opp]]."
  [[n int] [m int]]
  (==> (< (-- m) (-- n))
       (< n m)))

(proof lt-opp-conv
    :script
  (assume [H (< (-- m) (-- n))]
    ;; (elem int (- (-- n) (-- m)) int)))
    (have <a> (elem int (- (-- n) (-- m)) nat)
          :by (p/and-elim-left% H))
    (have <b> (not (= (-- m) (-- n)))
          :by (p/and-elim-right% H))
    (have <c> (= (- (-- n) (-- m))
                 (- m n))
          :by (eq/eq-sym% (minus/minus-opp m n)))
    (have <d> (<= n m)
          :by (eq/eq-subst% (lambda [k int] (elem int k nat))
                            <c> <a>))
    (assume [Heq (= n m)]
      (have <e1> (= m n) :by (eq/eq-sym% Heq))
      (have <e2> (= (-- m) (-- n))
            :by (eq/eq-cong% -- <e1>))
      (have <e> p/absurd :by (<b> <e2>)))
    (have <f> _ :by (p/and-intro% <d> <e>))
    (qed <f>)))

(defthm lt-opp-equiv
  "Property about [[<]] wrt. [[--]]."
  [[n int] [m int]]
  (<=> (< n m)
       (< (-- m) (-- n))))

(proof lt-opp-equiv
    :script
  (have <a> _ :by (p/and-intro% (lt-opp n m)
                                (lt-opp-conv n m)))
  (qed <a>))

(defthm lt-zero-opp
  [[n int]]
  (==> (< n zero)
       (> (-- n) zero)))

(proof lt-zero-opp
    :script
  (assume [H (< n zero)]
    (have <a> (elem int (-- n) nat)
          :by (p/and-elim-left% H))
    (have <b> (not (= n zero))
          :by (p/and-elim-right% H))
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
            :by (eq/eq-sym% (minus/minus-zero (-- n))))
      (have <e> (<= zero (-- n))
            :by (eq/eq-subst% (lambda [k int] (elem int k nat))
                              <e1> <a>))
      (assume [Heq (= zero (-- n))]
        (have <f1> (= (-- n) zero)
              :by (eq/eq-sym% Heq))
        (have <f2> (= n zero)
              :by ((minus/zero-opp-zero-conv n) <f1>))
        (have <f> p/absurd :by (<b> <f2>)))

      (have <g> (> (-- n) zero)
            :by (p/and-intro% <e> <f>)))

    (have <h> _ :by (p/or-elim% <c> (> (-- n) zero)
                                <d> <g>))
    (qed <h>)))

(defthm lt-zero-opp-conv
  [[n int]]
  (==> (> (-- n) zero)
       (< n zero)))

(proof lt-zero-opp-conv
    :script
  (assume [H (> (-- n) zero)]
    (have <a> (<= zero (-- n))  ;; (elem int (- (-- n) zero) nat)
          :by (p/and-elim-left% H))
    (have <b> (not (= zero (-- n)))
          :by (p/and-elim-right% H))
    (have <c> (elem int (-- n) nat)
          :by (eq/eq-subst% (lambda [k int] (elem int k nat))
                            (minus/minus-zero (-- n))
                            <a>))
    (have <d> (or (= n zero)
                  (negative n))
          :by ((minus/opp-nat-split n) <c>))
    "We proceed by case analysis."
    (assume [H1 (= n zero)]
      (have <e1> (= (-- n) zero) :by ((minus/zero-opp-zero n) H1))
      (have <e2> (= zero (-- n)) :by (eq/eq-sym% <e1>))
      (have <e3> p/absurd :by (<b> <e2>))
      (have <e> (< n zero) :by (<e3> (< n zero))))
    (assume [H2 (negative n)]
      (have <f> (< n zero) :by ((neg-lt-zero n) H2)))
    (have <g> _ :by (p/or-elim% <d> (< n zero) <e> <f>))
    (qed <g>)))

(defthm lt-zero-opp-equiv
  [[n int]]
  (<=> (< n zero)
       (> (-- n) zero)))

(proof lt-zero-opp-equiv
    :script
  (have <a> _ :by (p/and-intro% (lt-zero-opp n)
                                (lt-zero-opp-conv n)))
  (qed <a>))


(defthm minus-lt
  [[m int] [n int] [p int]]
  (==> (< (- m p) (- n p))
       (< m n)))

(proof minus-lt
    :script
  (assume [H (< (- m p) (- n p))]
    (have <a> (= (+ (- m p) p) m)
          :by (minus/minus-prop m p))
    (have <b> (= (+ (- n p) p) n)
          :by (minus/minus-prop n p))
    (have <c> (< (+ (- m p) p) (+ (- n p) p))
          :by ((plus-lt-conv (- m p) (- n p) p) H))
    (have <d> (< m (+ (- n p) p))
          :by (eq/eq-subst% (lambda [k int]
                              (< k (+ (- n p) p)))
                            <a> <c>))
    (have <e> (< m n)
          :by (eq/eq-subst% (lambda [k int]
                              (< m k))
                            <b> <d>))
    (qed <e>)))

(defthm minus-lt-conv
  [[m int] [n int] [p int]]
  (==> (< m n)
       (< (- m p) (- n p))))

(proof minus-lt-conv
    :script
  (assume [Hmn (< m n)]
    (have <a> (= (+ m (-- p)) (- m p))
          :by (minus/plus-opp-minus m p))
    (have <b> (= (+ n (-- p)) (- n p))
          :by (minus/plus-opp-minus n p))
    (have <c> (< (+ m (-- p)) (+ n (-- p)))
          :by ((plus-lt-conv m n (-- p)) Hmn))
    (have <d> (< (- m p) (+ n (-- p)))
          :by (eq/eq-subst% (lambda [k int]
                              (< k (+ n (-- p))))
                            <a> <c>))
    (have <e> (< (- m p) (- n p))
          :by (eq/eq-subst% (lambda [k int]
                              (< (- m p) k))
                            <b> <d>))
    (qed <e>)))

(defthm lt-succ
  "Strict ordering of successors."
  [[n int]]
  (< n (succ n)))

(proof lt-succ
    :script

  (have <a> (= (- (succ n) n)
               (succ (- n n)))
        :by (minus/minus-succ n n))

  (have <b> (= (succ (- n n))
               (succ zero))
        :by (eq/eq-cong% succ (minus/minus-cancel n)))

  (have <c1> (= (- (succ n) n)
               (succ zero))
        :by (eq/eq-trans% <a> <b>))

  (have <c> (= (succ zero)
               (- (succ n) n)) :by (eq/eq-sym% <c1>))

  (have <d> (elem int (succ zero) nat)
        :by ((nat/nat-succ zero) nat/nat-zero))

  (have <e> (<= n (succ n)) ;;(elem int (- (succ n) n) nat)
        :by (eq/eq-subst% (lambda [k int] (elem int k nat))
                          <c> <d>))
  (assume [Heq (= n (succ n))]
    (have <f1> (= (- n n) (- (succ n) n))
          :by (eq/eq-cong% (lambda [k int] (- k n))
                           Heq))
    (have <f2> (= zero (- (succ n) n))
          :by (eq/eq-subst% (lambda [k int] (= k (- (succ n) n)))
                            (minus/minus-cancel n)
                            <f1>))
    (have <f3> (= zero (succ zero))
          :by (eq/eq-subst% (lambda [k int] (= zero k))
                            <c1> <f2>))
    (have <f4> (= (succ zero) zero)
          :by (eq/eq-sym% <f3>))
    (have <f5> (not (= (succ zero) zero))
          :by ((nat/nat-zero-is-not-succ zero) nat/nat-zero))
    (have <f> p/absurd :by (<f5> <f4>)))

  (have <g> (< n (succ n)) :by (p/and-intro% <e> <f>))

  (qed <g>))


(defthm lt-succ-cong
  [[m int] [n int]]
  (==> (< m n)
       (< (succ m) (succ n))))

(proof lt-succ-cong
    :script
  (assume [Hmn (< m n)]
    (have <a> (= (+ m one) (succ m))
          :by (plus/plus-one m))
    (have <b> (= (+ n one) (succ n))
          :by (plus/plus-one n))
    (have <c> (< (+ m one) (+ n one))
          :by ((plus-lt-conv m n one) Hmn))
    (have <d> (< (succ m) (+ n one))
          :by (eq/eq-subst% (lambda [k int]
                              (< k (+ n one)))
                            <a> <c>))
    (have <e> (< (succ m) (succ n))
          :by (eq/eq-subst% (lambda [k int]
                              (< (succ m) k))
                            <b> <d>))
    (qed <e>)))


(defthm lt-pred
  [[m int]]
  (< (pred m) m))

(proof lt-pred
    :script
  (have <a> (< m (succ m))
        :by (lt-succ m))
  (have <b> (< (- m one) (- (succ m) one))
        :by ((minus-lt-conv m (succ m) one) <a>))
  (have <c> (= (- m one) (pred m))
        :by (minus/minus-one m))
  (have <d1> (= (- (succ m) one) (pred (succ m)))
        :by (minus/minus-one (succ m)))
  (have <d> (= (- (succ m) one) m)
        :by (eq/eq-subst% (lambda [k int]
                            (= (- (succ m) one) k))
                          (int/pred-of-succ m)
                          <d1>))
  (have <e> (< (pred m) (- (succ m) one))
        :by (eq/eq-subst% (lambda [k int]
                            (< k (- (succ m) one)))
                          <c> <b>))
  (have <f> (< (pred m) m)
        :by (eq/eq-subst% (lambda [k int]
                            (< (pred m) k))
                          <d> <e>))
  (qed <f>))


(defthm lt-succ-weak
  [[m int] [n int]]
  (==> (< m (succ n))
       (<= m n)))

(proof lt-succ-weak
    :script
  (assume [Hmn (< m (succ n))]
    (have <a> (elem int (- (succ n) m) nat)
          :by (p/and-elim-left% Hmn))
    (have <b> (elem int (succ (- n m)) nat)
          :by (eq/eq-subst% (lambda [k int]
                              (elem int k nat))
                            (minus/minus-succ n m)
                            <a>))
    "We use the nat-split principle."
    (have <c> (or (= (succ (- n m)) zero)
                  (positive (succ (- n m))))
          :by (nat/nat-split (succ (- n m)) <b>))
    (assume [Hzero (= (succ (- n m)) zero)]
      (have <d1> (= (succ (- n m)) (- (succ n) m))
            :by (eq/eq-sym% (minus/minus-succ n m)))
      (have <d2> (= (- (succ n) m) zero)
            :by (eq/eq-subst% (lambda [k int]
                                (= k zero))
                              <d1>
                              Hzero))
      (have <d3> (= m (succ n))
            :by ((eq/eq-sym int (succ n) m)
                 ((minus/minus-zero-conv (succ n) m) <d2>)))
      (have <d4> (not (= m (succ n)))
            :by (p/and-elim-right% Hmn))
      (have <d5> p/absurd :by (<d4> <d3>))
      (have <d> (<= m n) :by (<d5> (<= m n))))
    (assume [Hpos (positive (succ (- n m)))]
      (have <e> (<= m n)
            :by (eq/eq-subst% (lambda [k int]
                                (elem int k nat))
                              (int/pred-of-succ (- n m))
                              Hpos)))
    "We apply the split rule."
    (have <f> (<= m n) :by (p/or-elim% <c> (<= m n) <d> <e>))
    (qed <f>)))


(defthm pos-ge-one
  [[n int]]
  (==> (positive n)
       (>= n one)))

(proof pos-ge-one
    :script
  (assume [Hpos (positive n)]
    (have <a> (> n zero) :by ((pos-gt-zero n) Hpos))
    (have <b> (> (succ n) one)
          :by ((lt-succ-cong zero n) <a>))
    (have <c> (>= n one)
          :by ((lt-succ-weak one n) <b>))
    (qed <c>)))

;; (defthm pos-one-split
;;   "A split princple for positive numbers wrt. [[int/one]]."
;;   [[n int]]
;;   (==> (positive n)
;;        (or (= n one)
;;            (> n one))))

;; (proof pos-one-split
;;     :script
;;   (assume [Hn (positive n)]
;;     (have <a> (or (= (pred n) zero)
;;                   (positive (pred n)))
;;           :by (nat/nat-split (pred n) Hn))
;;     (assume [H1 (= (pred n) zero)]
;;       )))





