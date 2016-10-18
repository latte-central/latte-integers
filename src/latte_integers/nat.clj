(ns latte-integers.nat
  "The natural integers in ℕ as a subset of ℤ."

  (:refer-clojure :exclude [and or not int])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          lambda forall proof assume have
                                          ==>]]

            [latte.prop :as p :refer [and or not <=>]]

            [latte.equal :as eq :refer [equal]]

            [latte-integers.core :as int :refer [zero succ pred int]]

            [latte-sets.core :as set :refer [elem forall-in]]

            [latte.classic :as classic]))

(definition nat-succ-prop
  "A property verified by all successors of natural integers."
  [[P (==> int :type)]]
  (forall [y int] (==> (P y) (P (succ y)))))

(definition nat
  "The subset of natural integers."
  []
  (lambda [x int]
    (forall [P (==> int :type)]
      (==> (and (P zero)
                (nat-succ-prop P))
           (P x)))))

(defthm nat-zero
  "Zero is a natural integer."
  []
  (elem int zero nat))

(proof nat-zero :script
  (assume [P (==> int :type)
           H (and (P zero)
                  (nat-succ-prop P))]
    (have a (P zero) :by (p/and-elim-left% H))
    (qed a)))

(defthm nat-succ
  "The successor of a natural integer is a natural integer."
  [[x int]]
  (==> (elem int x nat)
       (elem int (succ x) nat)))

(proof nat-succ :script
  (assume [H (elem int x nat)]
    (assume [Q (==> int :type)
             H2 (and (Q zero)
                     (nat-succ-prop Q))]
      (have a (==> (and (Q zero)
                        (nat-succ-prop Q))
                   (Q x)) :by (H Q))
      (have b (Q x) :by (a H2))
      (have c (==> (Q x) (Q (succ x)))
            :by ((p/and-elim-right% H2) x))
      (have d (Q (succ x)) :by (c b))
      (qed d))))

(defaxiom nat-zero-has-no-pred
  "An important axiom of the natural integer subset
wrt. [[pred]]."
  []
  (not (elem int (pred zero) nat)))

(defthm nat-zero-is-not-succ
  "Zero is not a successor of a natural integer.

This is the first Peano 'axiom' (here theorem, based
 on integers) for natural integers."
  []
  (forall [x int]
    (==> (elem int x nat)
         (not (equal int (succ x) zero)))))

(proof nat-zero-is-not-succ :script
  (assume [x int
           H (elem int x nat)]
    (assume [H2 (equal int (succ x) zero)]
      (have a (equal int (pred (succ x)) (pred zero))
            :by ((eq/eq-cong int int pred (succ x) zero) H2))
      (have b (equal int x (pred (succ x)))
            :by ((eq/eq-sym int (pred (succ x)) x)
                 (int/pred-of-succ x)))
      (have c (equal int x (pred zero))
            :by ((eq/eq-trans int x (pred (succ x)) (pred zero))
                 b a))
      (have d (elem int (pred zero) nat)
            :by ((eq/eq-subst int nat x (pred zero))
                 c H))
      (have e p/absurd :by (nat-zero-has-no-pred d))
      (qed e))))

(defthm nat-succ-injective
  "Successor is injective, the second Peano 'axiom'
here a simple consequence of [[succ-injective]]."
  []
  (forall [x y int]
    (==> (elem int x nat)
         (elem int y nat)
         (equal int (succ x) (succ y))
         (equal int x y))))

(proof nat-succ-injective :script
  (assume [x int
           y int
           H1 (elem int x nat)
           H2 (elem int y nat)
           H3 (equal int (succ x) (succ y))]
    (have a (equal int x y)
          :by (int/succ-injective x y H3))
    (have b _ :discharge [H1 H2 H3 a])
    (qed b)))

(defthm nat-induct
  "The induction principle for natural integers.
This is the third Peano axiom but it can be
derived from [[int-induct]]."
  [[P (==> int :type)]]
  (==> (P zero)
       (forall [x int]
         (==> (elem int x nat)
              (P x)
              (P (succ x))))
       (forall [x int]
         (==> (elem int x nat)
              (P x)))))

(proof nat-induct :script
  (have Q _ :by (lambda [z int]
                  (and (elem int z nat)
                       (P z))))
  (assume [Hz (P zero)
           Hs (forall [x int]
                (==> (elem int x nat)
                     (P x)
                     (P (succ x))))]
    (have <a> (Q zero)
          :by (p/and-intro% 
               nat-zero Hz))
    (assume [y int
             Hy (Q y)]
      (have <b> (elem int y nat)
            :by (p/and-elim-left% Hy))
      (have <c> (P y)
            :by (p/and-elim-right% Hy))
      (have <d> (elem int (succ y) nat)
            :by ((nat-succ y) <b>))
      (have <e> (==> (P y) (P (succ y)))
            :by (Hs y <b>))
      (have <f> (P (succ y)) :by (<e> <c>))
      (have <g> (Q (succ y)) :by (p/and-intro% <d> <f>))
      (have <h> (nat-succ-prop Q) :discharge [y Hy <g>]))
    (have <i> (and (Q zero)
                   (nat-succ-prop Q)) :by (p/and-intro% <a> <h>))
    (assume [x int
             Hx (elem int x nat)]
      (have <j> (Q x) :by (Hx Q <i>))
      (have <k> (P x) :by (p/and-elim-right% <j>))
      (have <l> (forall [x int]
                  (==> (elem int x nat)
                       (P x))) :discharge [x Hx <k>])
      (qed <l>))))

(definition positive
  "The integer `n` is strictly positive."
  [[n int]]
  (elem int (pred n) nat))

(defthm positive-nat-split
  "Any non-zero natural number is positive."
  []
  (forall-in [x int nat]
    (==> (not (equal int x zero))
         (positive x))))

(proof positive-nat-split
    :script
  (have P _ :by (lambda [x int]
                  (==> (not (equal int x zero))
                       (elem int (pred x) nat))))
  "Let's proceed by induction"
  "First with (P zero)"
  (assume [Hnz (not (equal int zero zero))]
    (have <a1> (equal int zero zero) :by (eq/eq-refl int zero))
    (have <a2> p/absurd :by (Hnz <a1>))
    (have <a3> (elem int (pred zero) nat) :by (<a2> (elem int (pred zero) nat)))
    (have <a> (P zero) :discharge [Hnz <a3>]))
  "Then the inductive case."
  (assume [n int
           Hn (elem int n nat)
           Hind (P n)]
    "We aim to prove (P (succ n))"
    (assume [Hs (not (equal int (succ n) zero))]
      (have <b1> (equal int n (pred (succ n)))
            :by ((eq/eq-sym int (pred (succ n)) n) (int/pred-of-succ n)))
      (have <b2> (elem int (pred (succ n)) nat)
            :by ((eq/eq-subst int nat n (pred (succ n)))
                 <b1> Hn))
      (have <b3> (P (succ n)) :discharge [Hs <b2>]))
    (have <b> _ :discharge [n Hn Hind <b3>]))
  (have <c> (forall-in [x int nat] (P x))
        :by ((nat-induct P) <a> <b>))
  (qed <c>))


(defthm nat-case
  "Case analysis for natural numbers."
  [[P (==> int :type)]]
  (==> (P zero)
       (forall-in [k int nat] (P (succ k)))
       (forall-in [n int nat] (P n))))

(proof nat-case
    :script
  (assume [Hz (P zero)
           Hs (forall-in [k int nat] (P (succ k)))]
    "We proceed by induction on n"
    (have <a> (P zero) :by Hz)
    (assume [x int
             Hx (elem int x nat)
             HPx (P x)]
      (have <b1> (P (succ x)) :by (Hs x Hx))
      (have <b> (forall-in [k int nat]
                  (==> (P k) (P (succ k))))
            :discharge [x Hx HPx <b1>]))
    (have <c> _ :by ((nat-induct P) <a> <b>))
    (qed <c>)))

(defthm positive-succ
  "The successor of a natural number is positive."
  [[n int]]
  (==> (elem int n nat)
       (positive (succ n))))

(proof positive-succ
    :script
  (assume [Hn (elem int n nat)]
    (have <a> (not (equal int (succ n) zero))
          :by (nat-zero-is-not-succ n Hn))
    (have <b> (positive (succ n))
          :by (positive-nat-split (succ n)
                                  ((nat-succ n) Hn)
                                  <a>))
    (qed <b>)))

(defthm positive-succ-conv
  "A positive natural number is (obiously) a natural number"
  [[n int]]
  (==> (positive n)
       (elem int n nat)))

(proof positive-succ-conv
    :script
  (assume [H (positive n)]
    (have <a> (elem int (succ (pred n)) nat)
          :by ((nat-succ (pred n))
               H))
    (have <b> (elem int n nat)
          :by ((eq/eq-subst int nat (succ (pred n)) n)
               (int/succ-of-pred n)
               <a>))
    (qed <b>)))

(defthm positive-succ-strong
  "The successor of a positive is positive."
  [[n int]]
  (==> (positive n)
       (positive (succ n))))

(proof positive-succ-strong
    :script
  (assume [H (positive n)]
    (have <a> (elem int n nat) :by ((positive-succ-conv n) H))
    (have <b> (positive (succ n))
          :by ((positive-succ n) <a>))
    (qed <b>)))

(defthm nat-split
  "A natural number is either zero or it is positive"
  []
  (forall-in [n int nat] 
    (or (equal int n zero)
        (positive n))))

(proof nat-split
    :script
  (have P _ :by (lambda [k int]
                  (or (equal int k zero)
                      (positive k))))
  "We proceed by case analysis"
  (have <a> (P zero) :by ((p/or-intro-left (equal int zero zero)
                                           (positive zero))
                          (eq/eq-refl int zero)))
  (assume [n int
           Hn (elem int n nat)]
    (have <b1> (positive (succ n))
          :by ((positive-succ n) Hn))
    (have <b2> (or (equal int (succ n) zero)
                   (positive (succ n)))
          :by ((p/or-intro-right (equal int (succ n) zero)
                                 (positive (succ n)))
               <b1>))
    (have <b> (forall-in [n int nat] (P (succ n)))
          :discharge [n Hn <b2>]))
  (have <c> (forall-in [n int nat] (P n))
        :by ((nat-case P) <a> <b>))
  (qed <c>))

(definition negative
  "The integer `n` is strictly negative."
  [[n int]]
  (not (elem int n nat)))

(defthm int-split
  "The tripartition property about integers."
  [[n int]]
  (or (or (equal int n zero)
          (positive n))
      (negative n)))

(proof int-split
    :script
  (have <a> (or (elem int n nat)
                (not (elem int n nat)))
        :by (classic/excluded-middle-ax (elem int n nat)))
  (assume [Hyes (elem int n nat)]
    (have <b1> (or (equal int n zero)
                   (positive n))
          :by ((nat-split n) Hyes))
    (have <b2> _ :by ((p/or-intro-left (or (equal int n zero)
                                           (positive n))
                                       (negative n))
                      <b1>))
    (have <b> _ :discharge [Hyes <b2>]))
  (assume [Hno (not (elem int n nat))]
    (have <c1> (negative n) :by Hno)
    (have <c2> _ :by ((p/or-intro-right (or (equal int n zero)
                                            (positive n))
                                        (negative n))
                      <c1>))
    (have <c> _ :discharge [Hno <c2>]))
  (have <d> (or (or (equal int n zero)
                    (positive n))
                (negative n))
        :by ((p/or-elim (elem int n nat)
                        (not (elem int n nat)))
             <a>
             (or (or (equal int n zero)
                     (positive n))
                 (negative n))
             <b>
             <c>))
  (qed <d>))

;; The following is an attempt for a constructive
;; proof of int-split... which requires some
;; more informations about the fact of being
;; negative...
;;
;; (proof int-split
;;     :script
;;   "The proof is by induction on n"

;;   (have P _ :by (lambda [x int]
;;                   (or (or (equal int x zero)
;;                           (positive x))
;;                       (negative x))))

;;   "Base case: zero"
;;   (have <a1> (equal int zero zero)
;;         :by (eq/eq-refl int zero))
;;   (have <a2> (or (equal int zero zero)
;;                  (positive zero))
;;         :by ((p/or-intro-left (equal int zero zero)
;;                               (positive zero))
;;              <a1>))
;;   (have <a> (P zero)
;;         :by ((p/or-intro-left (or (equal int zero zero)
;;                                   (positive zero))
;;                               (negative zero))
;;              <a2>))
;;   "Inductive case"
;;   (assume [k int
;;            Hind (P k)]
;;     "Left-case"
;;     (assume [Hl (or (equal int k zero)
;;                     (positive k))]
;;       "Left-left case"
;;       (assume [Hll (equal int k zero)]
;;         (have <lla1> (elem int k nat)
;;               :by ((eq/eq-subst int nat zero k)
;;                    ((eq/eq-sym int k zero) Hll)
;;                    nat-zero))
;;         (have <lla2> (positive (succ k))
;;               :by ((positive-succ k) <lla1>))
;;         (have <lla3> (or (equal int (succ k) zero)
;;                          (positive (succ k)))
;;               :by ((p/or-intro-right (equal int (succ k) zero)
;;                                      (positive (succ k)))
;;                    <lla2>))
;;         (have <lla> (P (succ k))
;;               :by ((p/or-intro-left (or (equal int (succ k) zero)
;;                                         (positive (succ k)))
;;                                     (negative (succ k)))
;;                    <lla3>))
;;         (have <llb1> (negative (pred k))
;;               :by ((eq/eq-subst int
;;                                 (lambda [x int] (negative (pred x)))
;;                                 zero
;;                                 k)
;;                    ((eq/eq-sym int k zero) Hll)
;;                    nat-zero-has-no-pred))
;;         (have <llb> (P (pred k))
;;               :by ((p/or-intro-right (or (equal int (pred k) zero)
;;                                          (positive (pred k)))
;;                                      (negative (pred k)))
;;                    <llb1>))
;;         (have <llc> (and (P (succ k))
;;                          (P (pred k))) :by (p/and-intro% <lla> <llb>))
;;         (have <ll> _ :discharge [Hll <llc>]))
;;       "Left-right case"
;;       (assume [Hlr (positive k)]
;;         (have <lra1> (positive (succ k))
;;               :by ((positive-succ-strong k) Hlr))
;;         (have <lra2> (or (equal int (succ k) zero)
;;                          (positive (succ k)))
;;               :by ((p/or-intro-right (equal int (succ k) zero)
;;                                      (positive (succ k)))
;;                    <lra1>))
;;         (have <lra> (P (succ k))
;;               :by ((p/or-intro-left (or (equal int (succ k) zero)
;;                                         (positive (succ k)))
;;                                     (negative (succ k)))
;;                    <lra2>))
;;         (have <lrb1> (or (equal int (pred k) zero)
;;                          (positive (pred k)))
;;               :by (nat-split (pred k) Hlr))
;;         (have <lrb> (P (pred k))
;;               :by ((p/or-intro-left (or (equal int (pred k) zero)
;;                                         (positive (pred k)))
;;                                     (negative (pred k)))
;;                    <lrb1>))
;;         (have <lrc> (and (P (succ k))
;;                          (P (pred k)))
;;               :by (p/and-intro% <lra> <lrb>))
;;         (have <lr> _ :discharge [Hlr <lrc>]))
;;       (have <l1> (and (P (succ k))
;;                       (P (pred k)))
;;             :by ((p/or-elim (equal int k zero)
;;                             (positive k))
;;                  Hl (and (P (succ k))
;;                          (P (pred k))) <ll> <lr>))
;;       (have <l> _ :discharge [Hl <l1>]))
;;     "Right case"
;;     (assume [Hr (negative k)]
;;       )))
