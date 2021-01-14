
(ns latte-integers.plus
  "The addition defined on ℤ."

  (:refer-clojure :exclude [and or not int = +])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          pose try-proof qed]]

            [latte.utils :as u]
            
            [latte-prelude.prop :as p :refer [and or not <=>]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.fun :as fun]

            [latte-sets.set :as set :refer [elem]]
            [latte-sets.quant :as sq :refer [forall-in]]

            [latte-integers.int :as int :refer [zero one succ pred int =]]
            [latte-integers.nat :as nat :refer [nat positive negative]]
            [latte-integers.rec :as rec]))

(definition add-prop
  "The property of the addition function on integers."
  [[m int]]
  (lambda [g (==> int int)]
    (and (= (g zero) m)
         (forall [x int]
           (= (g (succ x)) (succ (g x)))))))

(defthm add-unique
  "The unicity of the addition function, through [[add-prop]]."
  [[m int]]
  (q/unique (add-prop m)))

(proof 'add-unique
  (qed (rec/int-recur-bijection m succ int/succ-bijective)))

(definition plus
  "The function that adds `m` to an integer"
  [[m int]]
  (q/the (add-unique m)))

(definition +
  "The function that adds `m` to `n`."
  [[m int] [n int]]
  ((plus m) n))

(defthm plus-prop
  [[m int]]
  (and (= ((plus m) zero) m)
       (forall [n int]
         (= ((plus m) (succ n))
            (succ ((plus m) n))))))

(proof 'plus-prop
  (qed (q/the-prop (add-unique m))))

(defthm plus-zero
  [[m int]]
  (= (+ m zero) m))

(proof 'plus-zero
  (qed (p/and-elim-left (plus-prop m))))

(defthm plus-succ
  [[m int] [n int]]
  (= (+ m (succ n))
     (succ (+ m n))))

(proof 'plus-succ
  (qed ((p/and-elim-right (plus-prop m)) n)))


;; make the basic definitions opaque
;; (otherwise terms become extra-large)
(u/set-opacity! #'plus-prop true)
(u/set-opacity! #'plus true)
(u/set-opacity! #'+ true)

(defthm plus-succ-sym
  [[m int] [n int]]
  (= (succ (+ m n))
     (+ m (succ n))))

(proof 'plus-succ-sym
  (qed (eq/eq-sym (plus-succ m n))))

(defthm plus-pred
  [[m int] [n int]]
  (= (+ m (pred n))
     (pred (+ m n))))

(proof 'plus-pred
  (have <a> (= (+ m (succ (pred n)))
               (succ (+ m (pred n))))
        :by (plus-succ m (pred n)))
  (have <b> (= (+ m n)
               (succ (+ m (pred n))))
        :by (eq/rewrite <a> (int/succ-of-pred n)))
  (have <c> (= (pred (+ m n))
               (pred (succ (+ m (pred n)))))
        :by (eq/eq-cong pred <b>))
  (have <d> (= (pred (+  m n))
               (+ m (pred n)))
        :by (eq/rewrite <c> (int/pred-of-succ (+ m (pred n)))))
  (qed (eq/eq-sym <d>)))


(defthm plus-pred-sym
  [[m int] [n int]]
  (= (pred (+ m n))
     (+ m (pred n))))

(proof 'plus-pred-sym
  (qed (eq/eq-sym (plus-pred m n))))


(defthm plus-zero-swap
  [[m int]]
  (= (+ zero m) m))

(proof 'plus-zero-swap
  "We proceed by induction on `m`."
  "First the case for m=0"
  (have <a> (= (+ zero zero) zero)
        :by (plus-zero zero))
  "Then the inductive case, we assume `(P m)` for some `m`."
  (assume [m int
           Hind (= (+ zero m) m)]
    "We must show `(P (pred m))`."
    (have <b1> (= (+ zero (pred m))
                  (pred (+ zero m)))
          :by (plus-pred zero m))
    (have <b> (= (+ zero (pred m))
                 (pred m))
          :by (eq/rewrite <b1> Hind))
    "and also  and `(P (succ m))`."
    (have <c1> (= (+ zero (succ m))
                  (succ (+ zero m)))
          :by (plus-succ zero m))
    (have <c> (= (+ zero (succ m))
                 (succ m))
          :by (eq/rewrite <c1> Hind))
    (have <d> _ :by (p/and-intro <c> <b>)))
  (qed (((int/int-induct (lambda [m int]
                                 (= (+ zero m) m)))
         <a> <d>) m)))

(defthm plus-succ-swap
  [[m int] [n int]]
  (= (+ (succ m) n)
     (succ (+ m n))))

(proof 'plus-succ-swap
  (have <a1> (= (+ (succ m) zero)
                (succ m))
        :by (plus-zero (succ m)))
  (have <a2> (= (succ m)
                (succ (+ m zero)))
        :by (eq/eq-cong succ (eq/eq-sym (plus-zero m))))
  (have <a> (= (+ (succ m) zero)
               (succ (+ m zero)))
        :by (eq/eq-trans <a1> <a2>))
  (assume [n int
           Hind (= (+ (succ m) n)
                   (succ (+ m n)))]
    "We first show `(P (pred n))`."
    (have <b1> (= (+ (succ m) (pred n))
                  (pred (+ (succ m) n)))
          :by (plus-pred (succ m) n))
    (have <b2> (= (pred (+ (succ m) n))
                  (pred (succ (+ m n))))
          :by (eq/eq-cong pred Hind))
    (have <b3> (= (+ (succ m) (pred n))
                  (pred (succ (+ m n))))
          :by (eq/eq-trans <b1> <b2>))
    (have <b4> (= (+ (succ m) (pred n))
                  (+ m n))
          :by (eq/rewrite <b3> (int/pred-of-succ (+ m n))))
    (have <b5> (= (+ m (succ (pred n)))
                  (succ (+ m (pred n))))
          :by (plus-succ m (pred n)))
    (have <b6> (= (+ m n)
                  (+ m (succ (pred n))))
          :by (eq/nrewrite 2 (eq/eq-refl (+ m n))
                           (eq/eq-sym (int/succ-of-pred n))))
    (have <b7> (= (+ m n)
                  (succ (+ m (pred n))))
          :by (eq/eq-trans <b6> <b5>))
    (have <b> (= (+ (succ m) (pred n))
                 (succ (+ m (pred n))))
          :by (eq/eq-trans <b4> <b7>))
    "And then `P (succ n)`."
    (have <c1> (= (+ (succ m) (succ n))
                  (succ (+ (succ m) n)))
          :by (plus-succ (succ m) n))
    (have <c2> (= (succ (+ (succ m) n))
                  (succ (succ (+ m n))))
          :by (eq/eq-cong succ Hind))
    (have <c3> (= (+ (succ m) (succ n))
                  (succ (succ (+ m n))))
          :by (eq/eq-trans <c1> <c2>))
    (have <c4> (= (succ (succ (+ m n)))
                  (succ (+ m (succ n))))
          :by (eq/eq-cong succ (eq/eq-sym (plus-succ m n))))
    (have <c> (= (+ (succ m) (succ n))
                 (succ (+ m (succ n))))
          :by (eq/eq-trans <c3> <c4>))
    "Let's conjunct the two sides."
    (have <d> _ :by (p/and-intro <c> <b>)))
  (qed (((int/int-induct (lambda [n int]
                           (= (+ (succ m) n)
                              (succ (+ m n)))))
         <a> <d>) n)))

(defthm plus-pred-swap
  [[m int] [n int]]
  (= (+ (pred m) n)
     (pred (+ m n))))

(proof 'plus-pred-swap
  (have <a> (= (+ (succ (pred m)) n)
               (succ (+ (pred m) n)))
        :by (plus-succ-swap (pred m) n))
  (have <b> (= (+ m n)
               (succ (+ (pred m) n)))
        :by (eq/rewrite <a> (int/succ-of-pred m)))
  (have <c> (= (pred (+ m n))
               (pred (succ (+ (pred m) n))))
        :by (eq/eq-cong pred <b>))
  (have <d> (= (pred (+ m n))
               (+ (pred m) n))
        :by (eq/rewrite <c> (int/pred-of-succ (+ (pred m) n))))
  (qed (eq/eq-sym <d>)))

(defthm plus-commute
  [[n int] [m int]]
  (= (+ n m)
     (+ m n)))

(proof 'plus-commute
  "We proceed by induction on `n`."
  (pose P := (lambda [k int] (= (+ k m) (+ m k))))
  "First let's prove `(P zero)`."
  (have <a1> (= m (+ m zero))
        :by (eq/eq-sym (plus-zero m)))
  (have <a> (P zero) :by (eq/eq-trans (plus-zero-swap m) <a1>))
  "Now the inductive cases."
  (assume [k int
           Hind (P k)]
    "First the succesor case, we show `(P (succ k))`."
    (have <b1> (= (+ (succ k) m)
                  (succ (+ k m)))
          :by (plus-succ-swap k m))
    (have <b2> (= (succ (+ k m))
                  (succ (+ m k)))
          :by (eq/eq-cong succ Hind))
    (have <b3> (= (+ (succ k) m)
                  (succ (+ m k))) :by (eq/eq-trans <b1> <b2>))
    (have <b4> (= (succ (+ m k))
                  (+ m (succ k))) :by (eq/eq-sym (plus-succ m k)))
    (have <b> (P (succ k)) :by (eq/eq-trans <b3> <b4>))
    "Second the predecessor case, we show `(P (pred k))`."
    (have <c1> (= (+ (pred k) m)
                  (pred (+ k m))) :by (plus-pred-swap k m))
    (have <c2> (= (pred (+ k m))
                  (pred (+ m k)))
          :by (eq/eq-cong pred Hind))
    (have <c3> (= (+ (pred k) m)
                  (pred (+ m k))) :by (eq/eq-trans <c1> <c2>))
    (have <c4> (= (pred (+ m k))
                  (+ m (pred k))) :by (eq/eq-sym (plus-pred m k)))
    (have <c> (P (pred k)) :by (eq/eq-trans <c3> <c4>))
    (have <d> _ :by (p/and-intro <b> <c>)))
  "Now we apply integer induction."
  (have <e> (P n) :by ((int/int-induct P) <a> <d> n))
  (qed <e>))

(defthm plus-pred-succ
  [[n int] [m int]]
  (= (+ (pred n) (succ m))
     (+ n m)))

(proof 'plus-pred-succ
  (have <a> (= (+ (pred n) (succ m))
               (pred (+ n (succ m))))
        :by (plus-pred-swap n (succ m)))
  (have <b> (= (+ n (succ m))
               (succ (+ n m))) :by (plus-succ n m))
  (have <c> (= (+ (pred n) (succ m))
               (pred (succ (+ n m))))
        :by (eq/rewrite <a> <b>))
  (have <d> (= (pred (succ (+ n m)))
               (+ n m))
        :by (int/pred-of-succ (+ n m)))
  (have <e> (= (+ (pred n) (succ m))
               (+ n m)) :by (eq/eq-trans <c> <d>))
  (qed <e>))

(defthm plus-succ-pred
  [[n int] [m int]]
  (= (+ (succ n) (pred m))
     (+ n m)))

(proof 'plus-succ-pred
  (have <a> (= (+ (succ n) (pred m))
               (+ (pred m) (succ n)))
        :by (plus-commute (succ n) (pred m)))
  (have <b> (= (+ (pred m) (succ n))
               (+ m n)) :by (plus-pred-succ m n))
  (have <c> (= (+ (succ n) (pred m))
               (+ m n)) :by (eq/eq-trans <a> <b>))
  (have <d> (= (+ m n) (+ n m))
        :by (plus-commute m n))
  (have <e> (= (+ (succ n) (pred m))
               (+ n m)) :by (eq/eq-trans <c> <d>))
  (qed <e>))

(defthm plus-assoc
  [[n int] [m int] [p int]]
  (= (+ n (+ m p))
     (+ (+ n m) p)))

(proof 'plus-assoc
  (pose P := (lambda [k int]
               (= (+ n (+ m k))
                  (+ (+ n m) k))))
  "We prove `P` by induction on `k`."
  "First `(P zero)`"
  (have <a1> (= (+ n (+ m zero))
                (+ n m))
        :by (eq/eq-cong (lambda [k int] (+ n k))
                         (plus-zero m)))
  (have <a2> (= (+ n m)
                (+ (+ n m) zero))
        :by (eq/eq-sym (plus-zero (+ n m))))
  (have <a> (P zero) :by (eq/eq-trans <a1> <a2>))
  "Then the inductive cases."
  (assume [p int
           Hind (= (+ n (+ m p))
                   (+ (+ n m) p))]
    "Let's prove `(P (succ p))`."
    (have <b1> (= (+ n (+ m (succ p)))
                  (+ n (succ (+ m p))))
          :by (eq/eq-cong (lambda [k int] (+ n k))
                          (plus-succ m p)))
    (have <b2>  (= (+ n (succ (+ m p)))
                   (succ (+ n (+ m p))))
          :by (plus-succ n (+ m p)))
    (have <b3> (= (+ n (+ m (succ p)))
                  (succ (+ n (+ m p))))
          :by (eq/eq-trans <b1> <b2>))
    (have <b4> (= (succ (+ n (+ m p)))
                  (succ (+ (+ n m) p)))
          :by (eq/eq-cong succ Hind))
    (have <b5> (= (+ n (+ m (succ p)))
                  (succ (+ (+ n m) p)))
          :by (eq/eq-trans <b3> <b4>))
    ;; = (+ (+ n m) (succ p))
    (have <b6> (= (succ (+ (+ n m) p))
                  (+ (+ n m) (succ p)))
          :by (eq/eq-sym (plus-succ (+ n m) p)))
    (have <b> (P (succ p))
          :by (eq/eq-trans <b5> <b6>))
    "and next prove `(P (pred p))`."
    (have <c1> (= (+ n (+ m (pred p)))
                  (+ n (pred (+ m p))))
          :by (eq/eq-cong (lambda [k int] (+ n k))
                          (plus-pred m p)))
    (have <c2> (= (+ n (pred (+ m p)))
                  (pred (+ n (+ m p))))
          :by (plus-pred n (+ m p)))
    (have <c3> (= (+ n (+ m (pred p)))
                  (pred (+ n (+ m p))))
          :by (eq/eq-trans <c1> <c2>))
    (have <c4> (= (pred (+ n (+ m p)))
                  (pred (+ (+ n m) p)))
          :by (eq/eq-cong pred Hind))
    (have <c5> (= (+ n (+ m (pred p)))
                   (pred (+ (+ n m) p)))
          :by (eq/eq-trans <c3> <c4>))
    ;; = (+ (+ n m) (pred p))
    (have <c6> (= (pred (+ (+ n m) p))
                  (+ (+ n m) (pred p)))
          :by (eq/eq-sym (plus-pred (+ n m) p)))
    (have <c> (P (pred p)) :by (eq/eq-trans <c5> <c6>))
    (have <d> _ :by (p/and-intro <b> <c>)))
  "Now we apply the integer induction."
  (have <e> (P p) :by ((int/int-induct P) <a> <d> p))
  (qed <e>))

(defthm plus-assoc-sym
  [[n int] [m int] [p int]]
  (= (+ (+ n m) p)
     (+ n (+ m p))))

(proof 'plus-assoc-sym
  (qed (eq/eq-sym (plus-assoc n m p))))

(defthm plus-right-cancel
  [[n int] [m int] [p int]]
  (==> (= (+ n p) (+ m p))
       (= n m)))

(proof 'plus-right-cancel
  "We proceed by induction."
  "Base case."
  (assume [Hz (= (+ n zero) (+ m zero))]
    (have <a1> (= n (+ m zero))
          :by (eq/rewrite Hz (plus-zero n)))
    (have <a> (= n m)
          :by (eq/rewrite <a1> (plus-zero m))))
  "Inductive cases."
  (assume [k int
           Hk (==> (= (+ n k) (+ m k))
                   (= n m))]
    "Successor case."
    (assume [Hsucc (= (+ n (succ k)) (+ m (succ k)))]
      (have <b1> (= (succ (+ n k)) (+ m (succ k)))
            :by (eq/rewrite Hsucc (plus-succ n k)))
      (have <b2> (= (succ (+ n k)) (succ (+ m k)))
            :by (eq/rewrite <b1> (plus-succ m k)))
      (have <b3> (= (+ n k) (+ m k)) :by (int/succ-injective (+ n k) (+ m k) <b2>))
      (have <b> (= n m) :by (Hk <b3>)))
    "Predecessor case."
    (assume [Hpred (= (+ n (pred k)) (+ m (pred k)))]
      (have <c1> (= (pred (+ n k)) (+ m (pred k)))
            :by (eq/rewrite Hpred (plus-pred n k)))
      (have <c2> (= (pred (+ n k)) (pred (+ m k)))
            :by (eq/rewrite <c1> (plus-pred m k)))
      (have <c3> (= (+ n k) (+ m k))
            :by (int/pred-injective (+ n k) (+ m k) <c2>))
      (have <c> (= n m) :by (Hk <c3>)))
    (have <d> _ :by (p/and-intro <b> <c>)))
  "We apply the induction principle."
  (have <e> _ :by ((int/int-induct (lambda [k int]
                                     (==> (= (+ n k) (+ m k))
                                          (= n m)))) <a> <d> p))
  (qed <e>))

(defthm plus-left-cancel
  [[n int] [m int] [p int]]
  (==>  (= (+ p n) (+ p m))
        (= n m)))

(proof 'plus-left-cancel
  (assume [H (= (+ p n) (+ p m))]
    (have <a> (= (+ n p) (+ p m))
          :by (eq/rewrite H (plus-commute p n)))
    (have <b> (= (+ n p) (+ m p))
          :by (eq/rewrite <a> (plus-commute p m)))
    (have <c> (= n m) :by ((plus-right-cancel n m p) <b>)))
  (qed <c>))

(defthm plus-right-cancel-conv
  [[n int] [m int] [p int]]
  (==> (= n m)
       (= (+ n p) (+ m p))))

(proof 'plus-right-cancel-conv
  (assume [H (= n m)]
    (have <a> (= (+ n p) (+ m p))
          :by (eq/eq-cong (lambda [k int] (+ k p))
                          H)))
  (qed <a>))

(defthm plus-left-cancel-conv
  [[n int] [m int] [p int]]
  (==> (= n m)
       (= (+ p n) (+ p m))))

(proof 'plus-left-cancel-conv
  (assume [H (= n m)]
    (have <a> (= (+ p n) (+ p m))
          :by (eq/eq-cong (lambda [k int] (+ p k))
                          H)))
  (qed <a>))


(defthm plus-nat-closed
  "The addition is closed for natural integers."
  []
  (forall-in [n nat]
    (forall-in [m nat]
      (elem (+ n m) nat))))

(proof 'plus-nat-closed
  (assume [n int
           Hn (elem n nat)]
    (pose P := (lambda [m int]
                       (elem (+ n m) nat)))
    "We prove `P` by natural induction."
    "First let's prove `(P zero)`."
    (have <a> (P zero)
          :by (eq/rewrite Hn (eq/eq-sym (plus-zero n))))
    "Then the inductive case."
    (assume [k int
             Hk (elem k nat)
             Hind (elem (+ n k) nat)]
      ;; proove: (elem int (+ n (succ k) nat))
      (have <b1> (elem (succ (+ n k)) nat)
            :by ((nat/nat-succ (+ n k)) Hind))
      (have <b> (P (succ k))
            :by (eq/rewrite <b1> (eq/eq-sym (plus-succ n k)))))
    "And finally we apply the induction principle."
    (have <c> (forall-in [m nat]
                (elem (+ n m) nat))
          :by ((nat/nat-induct P) <a> <b>)))
  (qed <c>))

(defthm positive-plus
  []
  (forall [n m int]
    (==> (positive n)
         (positive m)
         (positive (+ n m)))))

(proof 'positive-plus
  (assume [n int
           m int
           Hn (positive n)
           Hm (positive m)]
    (have <a> (elem (+ (pred n) (pred m)) nat)
          :by (plus-nat-closed (pred n) Hn (pred m) Hm))
    (have <b> (elem (pred (+ (pred n) m)) nat)
          :by (eq/rewrite <a> (plus-pred (pred n) m)))
    (have <c> (positive (pred (+ n m)))
          :by (eq/rewrite <b> (plus-pred-swap n m)))
    (have <d> (positive (succ (pred (+ n m))))
          :by ((nat/positive-succ-strong (pred (+ n m)))
               <c>))
    (have <e> (positive (+ n m))
          :by (eq/rewrite <d> (int/succ-of-pred (+ n m)))))
  (qed <e>))

(defthm negative-pos-plus
  []
  (forall [n int]
    (==> (nat/negative n)
         (exists [m int]
           (and (positive m)
                (= (+ n m) zero))))))

(proof 'negative-pos-plus
  "We prove this by integer induction."
  "Base case: `zero`"
  (assume [Hcontra (negative zero)]
    "We proceed by contradiction."
    (have <a1> p/absurd :by (Hcontra (nat/nat-zero)))
    (have <a> _
          :by (<a1> (exists [m int]
                      (and (positive m)
                           (= (+ zero m) zero))))))
  "Inductive cases."
  (assume [n int
           Hind (==> (negative n)
                     (exists [m int]
                       (and (positive m)
                            (= (+ n m) zero))))]
    "First, let's show the case for `(succ n)`."
    (assume [Hsucc (negative (succ n))]
      (have <b1> (negative (pred (succ n)))
            :by ((nat/negative-pred (succ n))
                 Hsucc))
      (have <b2> (negative n)
            :by (eq/rewrite <b1> (int/pred-of-succ n)))
      (have <b3> (exists [m int]
                   (and (positive m)
                        (= (+ n m) zero)))
            :by (Hind <b2>))
      (assume [m int
               Hm (and (positive m)
                       (= (+ n m) zero))]
        "We proceed by case analysis of `(pred n)`."
        (have <b4> (or (= (pred m) zero)
                       (positive (pred m)))
              :by (nat/nat-split (pred m) (p/and-elim-left Hm)))
        "First case: `(pred n)` is `zero`."
        (assume [Hmz (= (pred m) zero)]
          (have <c1> (= (succ (pred m)) (succ zero))
                :by (eq/eq-cong succ Hmz))
          (have <c2> (= m (succ zero))
                :by (eq/rewrite <c1> (int/succ-of-pred m)))
          (have <c3> (= (+ n (succ zero)) zero)
                :by (eq/rewrite (p/and-elim-right Hm) <c2>))
          (have <c4> (= (succ (+ n zero)) zero)
                :by (eq/rewrite <c3> (plus-succ n zero)))
          (have <c5> (= (pred (succ (+ n zero))) (pred zero))
                :by (eq/eq-cong pred <c4>))
          (have <c6> (= (+ n zero) (pred zero))
                :by (eq/rewrite <c5> (int/pred-of-succ (+ n zero))))
          (have <c7> (= n (pred zero))
                :by (eq/rewrite <c6> (plus-zero n)))
          (have <c8> (= (succ n) (succ (pred zero)))
                :by (eq/eq-cong succ <c7>))
          (have <c9> (= (succ n) zero)
                :by (eq/rewrite <c8> (int/succ-of-pred zero)))
          (have <c10> (elem (succ n) nat)
                :by (eq/rewrite (nat/nat-zero)
                                (eq/eq-sym <c9>)))
          (have <c11> p/absurd :by (Hsucc <c10>))
          (have <c> _
                :by (<c11> (and (positive (pred m))
                                (= (+ (succ n) (pred m)) zero)))))
        "Second case: `(pred n)` is (strictly) positive."
        (assume [Hmpos (positive (pred m))]
          (have <d1> (= (+ (succ n) (pred m))
                        (+ n m))
                :by (plus-succ-pred n m))
          (have <d2> (= (+ (succ n) (pred m))
                        zero)
                :by (eq/eq-trans <d1>
                                 (p/and-elim-right Hm)))
          (have <d> (and (positive (pred m))
                         (= (+ (succ n) (pred m)) zero))
                :by (p/and-intro Hmpos <d2>)))
        "Apply or-elimation."
        (have <e1> (and (positive (pred m))
                        (= (+ (succ n) (pred m)) zero))
              :by (p/or-elim <b4> <c> <d>))

        (have <e> (exists [p int]
                    (and (positive p)
                         (= (+ (succ n) p) zero)))
              :by ((q/ex-intro (lambda [p int]
                                       (and (positive p)
                                            (= (+ (succ n) p) zero)))
                               (pred m))
                   <e1>)))

      "The seeked propery hold for `(succ n)` (at last!)."
      (have <f> (exists [p int]
                  (and (positive p)
                       (= (+ (succ n) p) zero)))
            :by (q/ex-elim <b3> <e>)))
   
    "Second inductive case for `(pred n)`."
    (assume [Hpred (negative (pred n))]
      (have <g> (or (= n zero)
                    (negative n))
            :by ((nat/negative-pred-split n) Hpred))
      "We proceed by case."
      "First if `n` is `zero`."
      (assume [Hnz (= n zero)]
        (have <h1> (= (+ (pred zero) (succ zero))
                      (+ zero zero))
              :by (plus-pred-succ zero zero))
        (have <h2> (= (+ (pred zero) (succ zero))
                      zero)
              :by (eq/rewrite <h1> (plus-zero zero)))
        (have <h3> (= (+ (pred n) (succ zero))
                      zero)
              :by (eq/rewrite <h2> (eq/eq-sym Hnz)))        
        (have <h4> (positive (succ zero))
              :by ((nat/positive-succ zero)
                   (nat/nat-zero)))
        (have <h> (exists [p int]
                    (and (positive p)
                         (= (+ (pred n) p) zero)))
              :by ((q/ex-intro (lambda [p int]
                                 (and (positive p)
                                      (= (+ (pred n) p) zero)))
                               (succ zero))
                   (p/and-intro <h4> <h3>))))
      "Second if `n` is negative."
      (assume [Hnneg (negative n)]
        (have <i1> (exists [m int]
                       (and (positive m)
                            (= (+ n m) zero)))
              :by (Hind Hnneg))
        (assume [m int
                 Hm (and (positive m)
                         (= (+ n m) zero))]
          (have <i2> (= (+ (pred n) (succ m))
                        (+ n m))
                :by (plus-pred-succ n m))
          (have <i3> (= (+ (pred n) (succ m))
                        zero)
                :by (eq/eq-trans <i2> (p/and-elim-right Hm)))
          (have <i4> (positive (succ m))
                :by ((nat/positive-succ-strong m)
                     (p/and-elim-left Hm)))
          (have <i5> (exists [p int]
                       (and (positive p)
                            (= (+ (pred n) p) zero)))
                :by ((q/ex-intro (lambda [p int]
                                         (and (positive p)
                                              (= (+ (pred n) p) zero)))
                                 (succ m))
                     (p/and-intro <i4> <i3>))))
      
        (have <i> (exists [p int]
                    (and (positive p)
                         (= (+ (pred n) p) zero)))
              :by (q/ex-elim <i1> <i5>)))
      
      "or-elimination follows."
      (have <j> (exists [p int]
                  (and (positive p)
                       (= (+ (pred n) p) zero)))
            :by (p/or-elim <g> <h> <i>)))
    
    (have <k> _ :by (p/and-intro <f> <j>)))
  "We can finally apply the induction principle."
  (qed ((int/int-induct
         (lambda [n int]
                 (==> (nat/negative n)
                      (exists [m int]
                        (and (nat/positive m)
                             (= (+ n m) zero))))))
        <a> <k>)))

(defthm negative-pos-plus-conv
  []
  (forall [n int]
    (==> (exists [m int]
           (and (positive m)
                (= (+ n m) zero)))
         (negative n))))

(proof 'negative-pos-plus-conv
  (assume [n int
           Hex (exists [m int]
                 (and (positive m)
                      (= (+ n m) zero)))]
    (assume [m int
             Hm (and (positive m)
                     (= (+ n m) zero))]
      (have <a> (or (or (= n zero) (positive n))
                    (negative n)) :by (nat/int-split n))
      "First case: `n` is zero or positive."
      (assume [Hnl (or (= n zero) (positive n))]
        "Subcase: `n` is zero."
        (assume [Hnl1 (= n zero)]
          (have <b1> (= (+ zero m) zero)
                :by (eq/rewrite (p/and-elim-right Hm) Hnl1))
          (have <b2> (= m zero)
                :by (eq/rewrite <b1> (plus-zero-swap m)))
          (have <b3> (not (positive m))
                :by (eq/rewrite nat/nat-zero-has-no-pred
                                (eq/eq-sym <b2>)))
          (have <b4> p/absurd :by (<b3> (p/and-elim-left Hm)))
          (have <b> (negative n) :by (<b4> (negative n))))
        "Subcase: `n` is positive."
        (assume [Hnl2 (positive n)]
          (have <c1> (positive (+ n m))
                :by (positive-plus n m Hnl2 (p/and-elim-left Hm)))
          (have <c2> (not (positive (+ n m)))
                :by (eq/rewrite nat/nat-zero-has-no-pred (eq/eq-sym (p/and-elim-right Hm))))
          (have <c3> p/absurd :by (<c2> <c1>))
          (have <c> (negative n) :by (<c3> (negative n))))
        "Regroup the two subcases."
        (have <d> (negative n) :by (p/or-elim Hnl <b> <c>)))
      "Second case: `n` is negative"
      (assume [Hnr (negative n)]
        (have <e> (negative n) :by Hnr))
      "Regroup all the cases."
      (have <f> (negative n) :by (p/or-elim <a> <d> <e>)))
    (have <g> (negative n)
          :by (q/ex-elim Hex <f>)))
  (qed <g>))

(defthm negative-pos-plus-equiv
  [[n int]]
  (<=> (exists [m int]
         (and (positive m)
              (= (+ n m) zero)))
       (negative n)))

(proof 'negative-pos-plus-equiv
  (qed (p/and-intro (negative-pos-plus-conv n)
                    (negative-pos-plus n))))

(defthm negative-plus
  [[n int] [m int]]
  (==> (negative n)
       (negative m)
       (negative (+ n m))))

(proof 'negative-plus
  (assume [Hn (negative n)
           Hm (negative m)]
    (assume [p int
             Hp (and (positive p)
                     (= (+ n p) zero))]
      (assume [q int
               Hq (and (positive q)
                       (= (+ m q) zero))]
        (have <a> (positive (+ p q))
              :by (positive-plus p q
                                 (p/and-elim-left Hp)
                                 (p/and-elim-left Hq)))
        (have <b> (= (+ (+ n p) (+ m q)) (+ zero (+ m q)))
              :by ((plus-right-cancel-conv (+ n p) zero (+ m q))
                   (p/and-elim-right Hp)))
        (have <c> (= (+ (+ n p) (+ m q)) (+ zero zero))
              :by (eq/nrewrite 2 <b> (p/and-elim-right Hq)))
        (have <d> (= (+ (+ n p) (+ m q)) zero)
              :by (eq/rewrite <c> (plus-zero zero)))
        (have <e> (= (+ (+ (+ n p) m) q) zero)
              :by (eq/rewrite <d> (plus-assoc (+ n p) m q)))
        (have <f> (= (+ (+ n (+ p m)) q) zero)
              :by (eq/rewrite <e> (eq/eq-sym (plus-assoc n p m))))
        (have <g> (= (+ (+ n (+ m p)) q) zero)
              :by (eq/rewrite <f> (plus-commute p m)))
        (have <h> (= (+ (+ (+ n m) p) q) zero)
              :by (eq/rewrite <g> (plus-assoc n m p)))
        (have <i> (= (+ (+ n m) (+ p q)) zero)
              :by (eq/rewrite <h> (eq/eq-sym (plus-assoc (+ n m) p q))))
        (have <j> (exists [r int]
                    (and (positive r)
                         (= (+ (+ n m) r) zero)))
              :by ((q/ex-intro (lambda [r int]
                                 (and (positive r)
                                      (= (+ (+ n m) r) zero)))
                               (+ p q))
                   (p/and-intro <a> <i>)))
        (have <k> (negative (+ n m))
              :by (negative-pos-plus-conv (+ n m) <j>)))
      (have <l> (negative (+ n m))
            :by (q/ex-elim (negative-pos-plus m Hm) <k>)))
    (have <m> (negative (+ n m))
          :by (q/ex-elim (negative-pos-plus n Hn) <l>)))
  (qed <m>))

(defthm plus-one
  [[n int]]
  (= (+ n one)
     (succ n)))

(proof 'plus-one
  (have <a> (= (+ n one)
               (succ (+ n zero)))
        :by (plus-succ n zero))
  (have <b> (= (succ (+ n zero))
               (succ n))
        :by (eq/eq-cong succ (plus-zero n)))
  (have <c> (= (+ n one)
               (succ n))
        :by (eq/eq-trans <a> <b>))
  (qed <c>))


