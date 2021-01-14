(ns latte-integers.nat
  "The natural integers in ℕ as a subset of ℤ."

  (:refer-clojure :exclude [and or not int =])

  (:require [latte.core :as latte :refer [defaxiom defthm deflemma definition
                                          lambda forall proof assume have pose
                                          qed]]

            [latte.utils :as u]

            [latte-prelude.prop :as p :refer [and or not <=>]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.classic :as classic]

            
            [latte-sets.set :as set :refer [elem]]
            [latte-sets.quant :as setq :refer [forall-in]]

            [latte-integers.int :as int :refer [zero one succ pred int =]]))

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
  (elem zero nat))

(proof 'nat-zero
  (assume [P (==> int :type)
           H (and (P zero)
                  (nat-succ-prop P))]
    (have <a> (P zero) :by (p/and-elim-left H)))
  (qed <a>))

(defthm nat-succ
  "The successor of a natural integer is a natural integer."
  [[x int]]
  (==> (elem x nat)
       (elem (succ x) nat)))

(proof 'nat-succ
  (assume [H (elem x nat)]
    (assume [Q (==> int :type)
             H2 (and (Q zero)
                     (nat-succ-prop Q))]
      (have <a> (==> (and (Q zero)
                          (nat-succ-prop Q))
                     (Q x)) :by (H Q))
      (have <b> (Q x) :by (<a> H2))
      (have <c> (==> (Q x) (Q (succ x)))
            :by ((p/and-elim-right H2) x))
      (have <d> (Q (succ x)) :by (<c> <b>))))
  (qed <d>))

(defaxiom nat-zero-has-no-pred
  "An important axiom of the natural integer subset
wrt. [[pred]]."
  []
  (not (elem (pred zero) nat)))

(defthm nat-zero-is-not-succ
  "Zero is not a successor of a natural integer.

This is the first Peano 'axiom' (here theorem, based
 on integers) for natural integers."
  []
  (forall [x int]
    (==> (elem x nat)
         (not (= (succ x) zero)))))

(proof 'nat-zero-is-not-succ
    (assume [x int
             H (elem x nat)]
      (assume [H2 (= (succ x) zero)]
        (have <a> (= (pred (succ x)) (pred zero))
              :by (eq/eq-cong pred H2))
        (have <b> (= x (pred (succ x)))
              :by (eq/eq-sym (int/pred-of-succ x)))
        (have <c> (= x (pred zero))
              :by (eq/eq-trans <b> <a>))
        (have <d> (elem (pred zero) nat)
              :by (eq/rewrite H <c>))
        (have <e> p/absurd :by (nat-zero-has-no-pred <d>))))
  (qed <e>))

(defthm zero-is-not-one
  "A direct consequence of [[nat-zero-is-not-succ]]."
  []
  (not (= one zero)))

(proof 'zero-is-not-one
    (qed
     (nat-zero-is-not-succ zero nat-zero)))

(defthm nat-succ-injective
  "Successor is injective, the second Peano 'axiom'
here a simple consequence of [[succ-injective]]."
  []
  (forall [x y int]
    (==> (elem x nat)
         (elem y nat)
         (= (succ x) (succ y))
         (= x y))))

(proof 'nat-succ-injective
  (assume [x int
           y int
           H1 (elem x nat)
           H2 (elem y nat)
           H3 (= (succ x) (succ y))]
    (have <a> (= x y)
          :by (int/succ-injective x y H3)))
  (qed <a>))

(defthm nat-induct
  "The induction principle for natural integers.
This is the third Peano axiom but it can be
derived from [[int-induct]]."
  [[P (==> int :type)]]
  (==> (P zero)
       (forall [x int]
         (==> (elem x nat)
              (P x)
              (P (succ x))))
       (forall [x int]
         (==> (elem x nat)
              (P x)))))

(proof 'nat-induct
  (pose Q := (lambda [z int]
                     (and (elem z nat)
                          (P z))))
  (assume [Hz (P zero)
           Hs (forall [x int]
                      (==> (elem x nat)
                           (P x)
                           (P (succ x))))]
    (have <a> (Q zero)
          :by (p/and-intro nat-zero Hz))
    (assume [y int
             Hy (Q y)]
      (have <b> (elem y nat)
            :by (p/and-elim-left Hy))
      (have <c> (P y)
            :by (p/and-elim-right Hy))
      (have <d> (elem (succ y) nat)
            :by ((nat-succ y) <b>))
      (have <e> (==> (P y) (P (succ y)))
            :by (Hs y <b>))
      (have <f> (P (succ y)) :by (<e> <c>))
      (have <g> (Q (succ y)) :by (p/and-intro <d> <f>)))
    (have <h> (and (Q zero)
                   (nat-succ-prop Q)) :by (p/and-intro <a> <g>))
    (assume [x int
             Hx (elem x nat)]
      (have <i> (Q x) :by (Hx Q <h>))
      (have <j> (P x) :by (p/and-elim-right <i>))))
  (qed <j>))

(definition positive
  "The integer `n` is strictly positive."
  [[n int]]
  (elem (pred n) nat))

(defthm positive-nat-split
  "Any non-zero natural number is positive."
  []
  (forall-in [x nat]
    (==> (not (= x zero))
         (positive x))))

(proof 'positive-nat-split
  (pose P := (lambda [x int]
                (==> (not (= x zero))
                     (elem (pred x) nat))))
  "Let's proceed by induction"
  "First with (P zero)"
  (assume [Hnz (not (= zero zero))]
    (have <a1> (= zero zero) :by (eq/eq-refl zero))
    (have <a2> p/absurd :by (Hnz <a1>))
    (have <a> (elem (pred zero) nat) :by (<a2> (elem (pred zero) nat))))
  "Then the inductive case."
  (assume [n int
           Hn (elem n nat)
           Hind (P n)]
    "We aim to prove (P (succ n))"
    (assume [Hs (not (= (succ n) zero))]
      (have <b1> (= n (pred (succ n)))
            :by (eq/eq-sym (int/pred-of-succ n)))
      (have <b> (elem (pred (succ n)) nat)
            :by (eq/rewrite Hn <b1>))))
  (have <c> (forall-in [x nat] (P x))
        :by ((nat-induct P) <a> <b>))
  (qed <c>))

(defthm nat-case
  "Case analysis for natural numbers."
  [[P (==> int :type)]]
  (==> (P zero)
       (forall-in [k nat] (P (succ k)))
       (forall-in [n nat] (P n))))

(proof 'nat-case
  (assume [Hz (P zero)
           Hs (forall-in [k nat] (P (succ k)))]
    "We proceed by induction on n"
    (have <a> (P zero) :by Hz)
    (assume [x int
             Hx (elem x nat)
             HPx (P x)]
      (have <b> (P (succ x)) :by (Hs x Hx)))
    (have <c> _ :by ((nat-induct P) <a> <b>)))
  (qed <c>))

(defthm positive-succ
  "The successor of a natural number is positive."
  [[n int]]
  (==> (elem n nat)
       (positive (succ n))))

(proof 'positive-succ
  (assume [Hn (elem n nat)]
    (have <a> (not (= (succ n) zero))
          :by (nat-zero-is-not-succ n Hn))
    (have <b> (positive (succ n))
          :by (positive-nat-split (succ n)
                                  ((nat-succ n) Hn)
                                  <a>)))
  (qed <b>))

(defthm positive-conv
  "A positive natural number is (obiously) a natural number"
  [[n int]]
  (==> (positive n)
       (elem n nat)))

(proof 'positive-conv
  (assume [H (positive n)]
    (have <a> (elem (succ (pred n)) nat)
          :by ((nat-succ (pred n))
               H))
    (have <b> (elem n nat)
          :by (eq/rewrite <a> (int/succ-of-pred n))))
  (qed <b>))

(defthm positive-zero-conv
  "A positive or null number is ... natural"
  [[n int]]
  (==> (or (= n zero)
           (positive n))
       (elem n nat)))

(proof 'positive-zero-conv
  (assume [H (or (= n zero)
                 (positive n))]
    (assume [H1 (= n zero)]
      (have <a> (elem n nat)
            :by (eq/rewrite nat-zero (eq/eq-sym H1))))
    (assume [H2 (positive n)]
      (have <b> (elem n nat)
            :by ((positive-conv n) H2)))
    (have <c> (elem n nat)
          :by (p/or-elim H <a> <b>)))
  (qed <c>))

(defthm positive-succ-conv
  "A successor of a positive natural number 
is (obiously) a natural number"
  [[n int]]
  (==> (positive (succ n))
       (elem n nat)))

(proof 'positive-succ-conv
  (assume [H (positive (succ n))]
    (have <a> (elem n nat)
          :by (eq/rewrite H (int/pred-of-succ n))))
  (qed <a>))

(defthm positive-succ-strong
  "The successor of a positive is positive."
  [[n int]]
  (==> (positive n)
       (positive (succ n))))

(proof 'positive-succ-strong
  (assume [H (positive n)]
    (have <a> (elem n nat) :by ((positive-conv n) H))
    (have <b> (positive (succ n))
          :by ((positive-succ n) <a>)))
  (qed <b>))

(defthm positive-succ-equiv
  "A positive number is a natural number."
  [[n int]]
  (<=> (positive (succ n))
       (elem n nat)))

(proof 'positive-succ-equiv
  (have <a> (==> (positive (succ n))
                 (elem n nat))
        :by (positive-succ-conv n))
  (have <b> (==> (elem n nat)
                 (positive (succ n)))
        :by (positive-succ n))
  (qed (p/and-intro <a> <b>)))

(defthm nat-split
  "A natural number is either zero or it is positive"
  []
  (forall-in [n nat] 
    (or (= n zero)
        (positive n))))

(proof 'nat-split
  (pose P := (lambda [k int]
                     (or (= k zero)
                         (positive k))))
  "We proceed by case analysis"
  (have <a> (P zero) :by (p/or-intro-left (eq/eq-refl zero)
                                          (positive zero)))
  (assume [n int
           Hn (elem n nat)]
    (have <b1> (positive (succ n))
          :by ((positive-succ n) Hn))
    (have <b> (or (= (succ n) zero)
                  (positive (succ n)))
          :by (p/or-intro-right (= (succ n) zero)
                                <b1>)))
  (have <c> (forall-in [n nat] (P n))
        :by ((nat-case P) <a> <b>))
  (qed <c>))

(defthm positive-succ-split
  "A positive successor can split."
  [[n int]]
  (==> (positive (succ n))
       (or (= n zero)
           (positive n))))

(proof 'positive-succ-split
  (assume [H (positive (succ n))]
    (have <a> (elem n nat)
          :by ((positive-succ-conv n) H))
    (have <b> (or (= n zero)
                  (positive n))
          :by (nat-split n <a>)))
  (qed <b>))

(defthm positive-succ-split-conv
  "The converse of [[positive-succ-split]]."
  [[n int]]
  (==> (or (= n zero)
           (positive n))
       (positive (succ n))))

(proof 'positive-succ-split-conv
  (assume [H (or (= n zero)
                 (positive n))]
    (assume [H1 (= n zero)]
      (have <a1> (elem n nat)
            :by (eq/rewrite nat-zero (eq/eq-sym H1)))
      (have <a> (positive (succ n))
            :by ((positive-succ n) <a1>)))
    (assume [H2 (positive n)]
      (have <b> (positive (succ n))
            :by ((positive-succ-strong n) H2)))
    (have <c> (positive (succ n))
          :by (p/or-elim H <a> <b>)))
  (qed <c>))

(defthm positive-succ-split-equiv
  "The conjunction of [[positive-succ-split]]
and [[positive-succ-split-conv]]."
  [[n int]]
  (<=> (positive (succ n))
       (or (= n zero)
           (positive n))))

(proof 'positive-succ-split-equiv
  (qed (p/and-intro (positive-succ-split n)
                    (positive-succ-split-conv n))))


(definition negative
  "The integer `n` is strictly negative."
  [[n int]]
  (not (elem n nat)))

(defthm int-split
  "The tripartition property about integers."
  [[n int]]
  (or (or (= n zero)
          (positive n))
      (negative n)))

(proof 'int-split
  (have <a> (or (elem n nat)
                (not (elem n nat)))
        :by (classic/excluded-middle-ax (elem n nat)))
  (assume [Hyes (elem n nat)]
    (have <b1> (or (= n zero)
                   (positive n))
          :by ((nat-split n) Hyes))
    (have <b> _ :by (p/or-intro-left <b1> (negative n))))
  (assume [Hno (not (elem n nat))]
    (have <c1> (negative n) :by Hno)
    (have <c> _ :by (p/or-intro-right (or (= n zero)
                                          (positive n))
                                      <c1>)))
  (qed (p/or-elim <a> <b> <c>)))

(defthm int-split-elim-rule
  "An elimination principle for integers."
  [[A :type]]
  (forall [n int]
    (==> (==> (= n zero) A)
         (==> (positive n) A)
         (==> (negative n) A)
         A)))

(proof 'int-split-elim-rule
  (assume [n int
           H1 (==> (= n zero) A)
           H2 (==> (positive n) A)
           H3 (==> (negative n) A)]
    "We want to apply the int-split principle."
    (assume [Hzp (or (= n zero) (positive n))]
      (assume [Hz (= n zero)]
        (have <a> A :by (H1 Hz)))
      (assume [Hp (positive n)]
        (have <b> A :by (H2 Hp)))
      (have <c> A :by (p/or-elim Hzp <a> <b>)))
    (assume [Hn (negative n)]
      (have <d> A :by (H3 Hn)))
    (have <e> A :by (p/or-elim (int-split n) <c> <d>)))
  (qed <e>))

(defthm int-split-elim
  "An elimination princile for integers, cf. [[int-split-elim-rule]]."
  [[?A :type] [n int] [pz (==> (= n zero) A)] [ppos (==> (positive n) A)] [pneg (==> (negative n) A)]]
  A)

(proof 'int-split-elim-thm
  (qed ((int-split-elim-rule A) n pz ppos pneg)))

;; The following is an attempt for a constructive
;; proof of int-split... which requires some
;; more informations about the fact of being
;; negative...
;;
;; (proof int-split
;; ;;   "The proof is by induction on n"

;;   (have P _ :by (lambda [x int]
;;                   (or (or (= x zero)
;;                           (positive x))
;;                       (negative x))))

;;   "Base case: zero"
;;   (have <a1> (= zero zero)
;;         :by (eq/eq-refl int zero))
;;   (have <a2> (or (= zero zero)
;;                  (positive zero))
;;         :by ((p/or-intro-left (= zero zero)
;;                               (positive zero))
;;              <a1>))
;;   (have <a> (P zero)
;;         :by ((p/or-intro-left (or (= zero zero)
;;                                   (positive zero))
;;                               (negative zero))
;;              <a2>))
;;   "Inductive case"
;;   (assume [k int
;;            Hind (P k)]
;;     "Left-case"
;;     (assume [Hl (or (= k zero)
;;                     (positive k))]
;;       "Left-left case"
;;       (assume [Hll (= k zero)]
;;         (have <lla1> (elem k nat)
;;               :by ((eq/eq-subst int nat zero k)
;;                    ((eq/eq-sym int k zero) Hll)
;;                    nat-zero))
;;         (have <lla2> (positive (succ k))
;;               :by ((positive-succ k) <lla1>))
;;         (have <lla3> (or (= (succ k) zero)
;;                          (positive (succ k)))
;;               :by ((p/or-intro-right (= (succ k) zero)
;;                                      (positive (succ k)))
;;                    <lla2>))
;;         (have <lla> (P (succ k))
;;               :by ((p/or-intro-left (or (= (succ k) zero)
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
;;               :by ((p/or-intro-right (or (= (pred k) zero)
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
;;         (have <lra2> (or (= (succ k) zero)
;;                          (positive (succ k)))
;;               :by ((p/or-intro-right (= (succ k) zero)
;;                                      (positive (succ k)))
;;                    <lra1>))
;;         (have <lra> (P (succ k))
;;               :by ((p/or-intro-left (or (= (succ k) zero)
;;                                         (positive (succ k)))
;;                                     (negative (succ k)))
;;                    <lra2>))
;;         (have <lrb1> (or (= (pred k) zero)
;;                          (positive (pred k)))
;;               :by (nat-split (pred k) Hlr))
;;         (have <lrb> (P (pred k))
;;               :by ((p/or-intro-left (or (= (pred k) zero)
;;                                         (positive (pred k)))
;;                                     (negative (pred k)))
;;                    <lrb1>))
;;         (have <lrc> (and (P (succ k))
;;                          (P (pred k)))
;;               :by (p/and-intro% <lra> <lrb>))
;;         (have <lr> _ :discharge [Hlr <lrc>]))
;;       (have <l1> (and (P (succ k))
;;                       (P (pred k)))
;;             :by ((p/or-elim (= k zero)
;;                             (positive k))
;;                  Hl (and (P (succ k))
;;                          (P (pred k))) <ll> <lr>))
;;       (have <l> _ :discharge [Hl <l1>]))
;;     "Right case"
;;     (assume [Hr (negative k)]
;;       )))


(defthm negative-nat
  []
  (forall-in [n nat]
    (not (negative n))))

(proof 'negative-nat
  (assume [n int
           Hn (elem n nat)]
    (assume [Hneg (negative n)]
      (have <a> p/absurd :by (Hneg Hn))))
  (qed <a>))

(defthm int-split-alt
  "An alternative split principle for integers
(or a constructive excluded middle principle, so to speak)."
  [[n int]]
  (or (elem n nat)
      (not (elem n nat))))

(proof 'int-split-alt
  (have <or> (or (or (= n zero)
                     (positive n))
                 (negative n)) :by (int-split n))
  (assume [H1 (or (= n zero)
                  (positive n))]
    (have <a1> (elem n nat)
          :by ((positive-zero-conv n) H1))
    (have <a> _
          :by (p/or-intro-left <a1>
                               (not (elem n nat)))))
  (assume [H2 (negative n)]
    (have <b1> (not (elem n nat)) :by H2)
    (have <b> _
          :by (p/or-intro-right (elem n nat)
                                <b1>)))
  (qed (p/or-elim <or> <a> <b>)))

(defthm negative-pred
  "Negative predecessors."
  [[n int]]
  (==> (negative n)
       (negative (pred n))))

(proof 'negative-pred
  (assume [Hn (negative n)]
    (have <split> (or (elem (pred n) nat)
                      (not (elem (pred n) nat)))
          :by (int-split-alt (pred n)))
    (assume [H1 (elem (pred n) nat)]
      (have <a1> (elem (succ (pred n)) nat)
            :by ((nat-succ (pred n))
                 H1))
      (have <a2> (elem n nat)
            :by (eq/rewrite <a1> (int/succ-of-pred n)))
      (have <a3> p/absurd :by (Hn <a2>))
      (have <a> (negative (pred n))
            :by (<a3> (negative (pred n)))))
    (assume [H2 (not (elem (pred n) nat))]
      (have <b> (negative (pred n)) :by H2))
    (have <c> (negative (pred n))
          :by (p/or-elim <split> <a> <b>)))
  (qed <c>))

(defthm negative-pred-zero
  "The predecessor of zero is negative."
  []
  (negative (pred zero)))

(proof 'negative-pred-zero
  (qed nat-zero-has-no-pred))

(defthm negative-pred-split-conv
  "An auxiliary theorem for the predecessor."
  [[n int]]
  (==> (or (= n zero)
           (negative n))
       (negative (pred n))))

(proof 'negative-pred-split-conv
  (assume [H (or (= n zero)
                 (negative n))]
    (assume [H1 (= n zero)]
      (have <a> (negative (pred n))
            :by (eq/rewrite negative-pred-zero
                            (eq/eq-sym H1))))
    (assume [H2 (negative n)]
      (have <b> (negative (pred n))
            :by ((negative-pred n) H2)))
    (have <c> (negative (pred n))
          :by (p/or-elim H <a> <b>)))
  (qed <c>))


(defthm negative-pred-split
  "Splitting of a predecessor."
  [[n int]]
  (==> (negative (pred n))
       (or (= n zero)
           (negative n))))

(proof 'negative-pred-split
  (assume [H (negative (pred n))]
    (have <split> (or (or (= n zero)
                          (positive n))
                      (negative n))
          :by (int-split n))
    (assume [H1 (or (= n zero)
                    (positive n))]
      (assume [Hz (= n zero)]
        (have <a> (or (= n zero)
                      (negative n))
              :by (p/or-intro-left Hz
                                   (negative n))))
      (assume [Hpos (positive n)]
        (have <b1> p/absurd :by (H Hpos))
        (have <b> (or (= n zero)
                      (negative n))
              :by (<b1> (or (= n zero)
                            (negative n)))))
      (have <c> (or (= n zero)
                    (negative n)) :by (p/or-elim H1 <a> <b>)))
    (assume [H2 (negative n)]
      (have <d> (or (= n zero)
                     (negative n))
            :by (p/or-intro-right (= n zero)
                                  H2)))
    (have <e> (or (= n zero)
                  (negative n)) :by (p/or-elim <split> <c> <d>)))
  (qed <e>))

(defthm negative-pred-split-equiv
  "The conjunction of [[negative-pred-split]]
and [[negative-pred-split-conv]]."
  [[n int]]
  (<=> (negative (pred n))
       (or (= n zero)
           (negative n))))

(proof 'negative-pred-split-equiv
  (qed (p/iff-intro (negative-pred-split n)
                    (negative-pred-split-conv n))))

(defthm negative-not-zero
  []
  (not (negative zero)))

(proof 'negative-not-zero
  (assume [H (negative zero)]
    (have <a> p/absurd :by (H nat-zero)))
  (qed <a>))

(defthm positive-not-zero
  []
  (not (positive zero)))

(proof 'positive-not-zero
  (assume [H (positive zero)]
    (have <a> p/absurd :by (nat-zero-has-no-pred H)))
  (qed <a>))

(defthm int-split-zero
  "Yet another split principle for integers."
  [[n int]]
  (or (= n zero)
      (not (= n zero))))

(proof 'int-split-zero
  (assume [H1 (= n zero)]
    (have <a> (or (= n zero)
                  (not (= n zero)))
          :by (p/or-intro-left H1 (not (= n zero)))))
  (assume [H2 (positive n)]
    (assume [H2' (= n zero)]
      (have <b1> (positive zero)
            :by (eq/rewrite H2 H2'))
      (have <b2> p/absurd :by (positive-not-zero <b1>)))
    (have <b> (or (= n zero)
                  (not (= n zero)))
          :by (p/or-intro-right (= n zero) <b2>)))
  (assume [H3 (negative n)]
    (assume [H3' (= n zero)]
      (have <c1> (negative zero)
            :by (eq/rewrite H3 H3'))
      (have <c2> p/absurd :by (negative-not-zero <c1>)))
    (have <c> (or (= n zero)
                  (not (= n zero)))
          :by (p/or-intro-right (= n zero) <c2>)))
  "We apply the more general integer splitting principle."
  (qed (int-split-elim n <a> <b> <c>)))

;; opacity
(u/set-opacity! #'nat true)
