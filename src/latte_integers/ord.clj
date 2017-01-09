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

            [latte-integers.core :as int :refer [zero succ pred int =]]
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
                              (plus/plus-zero-sym n)
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

(definition >=
  "The greater-or-equal order for integers."
  [[n int] [m int]]
  (<= m n))

(definition >
  "The strict variant of [[>=]]."
  [[n int] [m int]]
  (< m n))


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

(defthm plus-lt
  [[n int] [m int] [p int]]
  (==> (< (+ n p) (+ m p))
       (< n m)))

(defthm plus-le-conv
  "The converse of [[plus-le]]."
  [[n int] [m int] [p int]]
  (==> (<= n m)
       (<= (+ n p) (+ m p))))

(proof plus-le-conv
    :script
  (assume [H (<= n m)]
    ;; (elem int (- m n) nat)
    ;; (- m n)
    ;; = (+ (- m n) (- p p))    by minus-cancel and plus-zero
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
    ;; = (- (+ p m) (+ p n))    by assoc-minus-plus-sym
    (have <e> (elem int (- (+ p m) (+ p n)) nat)
          :by ((eq/eq-subst int (lambda [k int] (elem int k nat))
                            (- (- (+ p m) n) p)
                            (- (+ p m) (+ p n)))
               (eq/eq-sym% (minus/assoc-minus-plus (+ p m) n p))
               <d>))
    ;; = (- (+ m p) (+ n p))    by plus-commute
    ))

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



