
(ns latte-integers.plus
  "The addition defined on ℤ."

  (:refer-clojure :exclude [and or not int = +])

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
  (q/unique (==> int int)
            (add-prop m)))

(proof add-unique
    :term
  (rec/int-recur-bijection int m succ int/succ-bijective))

(definition plus
  "The function that adds `m` to an integer"
  [[m int]]
  (q/the (==> int int)
         (add-prop m)
         (add-unique m)))

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

(proof plus-prop
    :term
  (q/the-prop
      (==> int int)
    (add-prop m)
    (add-unique m)))

(defthm plus-zero
  [[m int]]
  (= (+ m zero) m))

(proof plus-zero
    :script
  (have <a> _ :by (p/and-elim-left% (plus-prop m)))
  (qed <a>))

(defthm plus-succ
  [[m int] [n int]]
  (= (+ m (succ n))
     (succ (+ m n))))

(proof plus-succ
    :script
  (have <a> _ :by ((p/and-elim-right% (plus-prop m)) n))
  (qed <a>))


(defthm plus-pred
  [[m int] [n int]]
  (= (+ m (pred n))
     (pred (+ m n))))

(proof plus-pred
    :script
  (have <a> (= (+ m (succ (pred n)))
               (succ (+ m (pred n))))
        :by (plus-succ m (pred n)))
  (have <b> (= (+ m n)
               (succ (+ m (pred n))))
        :by (eq/eq-subst%
             (lambda [k int]
               (= (+ m k)
                  (succ (+ m (pred n)))))
             (int/succ-of-pred n)
             <a>))
  (have <c> (= (pred (+ m n))
               (pred (succ (+ m (pred n)))))
        :by (eq/eq-cong% pred <b>))
  (have <d> (= (pred (+  m n))
               (+ m (pred n)))
        :by (eq/eq-subst% (lambda [k int]
                            (= (pred (+ m n)) k))
                          (int/pred-of-succ (+ m (pred n)))
                          <c>))
  (have <e> _ :by (eq/eq-sym% <d>))
  (qed <e>))

(defthm plus-zero-sym
  [[m int]]
  (= (+ zero m) m))

(proof plus-zero-sym
    :script
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
          :by (eq/eq-subst% (lambda [k int]
                              (= (+ zero (pred m))
                                 (pred k)))
                            Hind <b1>))
    "and also  and `(P (succ m))`."
    (have <c1> (= (+ zero (succ m))
                  (succ (+ zero m)))
          :by (plus-succ zero m))
    (have <c> (= (+ zero (succ m))
                 (succ m))
          :by (eq/eq-subst% (lambda [k int]
                             (= (+ zero (succ m))
                                (succ k)))
                            Hind <c1>))
    (have <d> _ :by (p/and-intro% <c> <b>)))
  (qed (((int/int-induct (lambda [m int]
                           (= (+ zero m) m)))
         <a> <d>) m)))

(defthm plus-succ-sym
  [[m int] [n int]]
  (= (+ (succ m) n)
     (succ (+ m n))))

(proof plus-succ-sym
    :script
  (have <a1> (= (+ (succ m) zero)
                (succ m))
        :by (plus-zero (succ m)))
  (have <a2> (= (succ m)
                (succ (+ m zero)))
        :by ((eq/eq-cong int int succ m (+ m zero))
             (eq/eq-sym% (plus-zero m))))
  (have <a> (= (+ (succ m) zero)
               (succ (+ m zero)))
        :by (eq/eq-trans% <a1> <a2>))
  (assume [n int
           Hind (= (+ (succ m) n)
                   (succ (+ m n)))]
    "We first show `(P (pred n))`."
    (have <b1> (= (+ (succ m) (pred n))
                  (pred (+ (succ m) n)))
          :by (plus-pred (succ m) n))
    (have <b2> (= (pred (+ (succ m) n))
                  (pred (succ (+ m n))))
          :by (eq/eq-cong% pred Hind))
    (have <b3> (= (+ (succ m) (pred n))
                  (pred (succ (+ m n))))
          :by (eq/eq-trans% <b1> <b2>))
    (have <b4> (= (+ (succ m) (pred n))
                  (+ m n))
          :by (eq/eq-subst% (lambda [k int]
                              (= (+ (succ m) (pred n))
                                 k))
                            (int/pred-of-succ (+ m n))
                        <b3>))
    (have <b5> (= (+ m (succ (pred n)))
                  (succ (+ m (pred n))))
          :by (plus-succ m (pred n)))
    (have <b6> (= (+ m n)
                  (+ m (succ (pred n))))
          :by ((eq/eq-subst int
                            (lambda [k int]
                              (= (+ m n)
                                 (+ m k)))
                            n
                            (succ (pred n)))
               (eq/eq-sym% (int/succ-of-pred n))
               (eq/eq-refl int (+ m n))))
    (have <b7> (= (+ m n)
                  (succ (+ m (pred n))))
          :by (eq/eq-trans% <b6> <b5>))
    (have <b> (= (+ (succ m) (pred n))
                 (succ (+ m (pred n))))
          :by (eq/eq-trans% <b4> <b7>))
    "And then `P (succ n)`."
    (have <c1> (= (+ (succ m) (succ n))
                  (succ (+ (succ m) n)))
          :by (plus-succ (succ m) n))
    (have <c2> (= (succ (+ (succ m) n))
                  (succ (succ (+ m n))))
          :by (eq/eq-cong% succ Hind))
    (have <c3> (= (+ (succ m) (succ n))
                  (succ (succ (+ m n))))
          :by (eq/eq-trans% <c1> <c2>))
    (have <c4> (= (succ (succ (+ m n)))
                  (succ (+ m (succ n))))
          :by ((eq/eq-cong int int succ
                           (succ (+ m n))
                           (+ m (succ n)))
               (eq/eq-sym% (plus-succ m n))))
    (have <c> (= (+ (succ m) (succ n))
                 (succ (+ m (succ n))))
          :by (eq/eq-trans% <c3> <c4>))
    "Let's conjunct the two sides."
    (have <d> _ :by (p/and-intro% <c> <b>)))
  (qed (((int/int-induct (lambda [n int]
                           (= (+ (succ m) n)
                              (succ (+ m n)))))
         <a> <d>) n)))

(defthm plus-pred-sym
  [[m int] [n int]]
  (= (+ (pred m) n)
     (pred (+ m n))))

(proof plus-pred-sym
    :script
  (have <a> (= (+ (succ (pred m)) n)
               (succ (+ (pred m) n)))
        :by (plus-succ-sym (pred m) n))
  (have <b> (= (+ m n)
               (succ (+ (pred m) n)))
        :by (eq/eq-subst% (lambda [k int]
                            (= (+ k n)
                               (succ (+ (pred m) n))))
                          (int/succ-of-pred m)
                          <a>))
  (have <c> (= (pred (+ m n))
               (pred (succ (+ (pred m) n))))
        :by (eq/eq-cong% pred <b>))
  (have <d> (= (pred (+ m n))
               (+ (pred m) n))
        :by (eq/eq-subst% (lambda [k int]
                            (= (pred (+ m n))
                               k))
                          (int/pred-of-succ (+ (pred m) n))
                          <c>))
  (qed ((eq/eq-sym int (pred (+ m n))
                   (+ (pred m) n)) <d>)))


(defthm plus-commute
  [[n int] [m int]]
  (= (+ n m)
     (+ m n)))

(proof plus-commute
    :script
  "We proceed by induction on `n`."
  (have P _ :by (lambda [k int] (= (+ k m) (+ m k))))
  "First let's prove `(P zero)`."
  (have <a1> (= m (+ m zero))
        :by (eq/eq-sym% (plus-zero m)))
  (have <a> (P zero) :by (eq/eq-trans% (plus-zero-sym m) <a1>))
  "Now the inductive cases."
  (assume [k int
           Hind (P k)]
    "First the succesor case, we show `(P (succ k))`."
    (have <b1> (= (+ (succ k) m)
                  (succ (+ k m)))
          :by (plus-succ-sym k m))
    (have <b2> (= (succ (+ k m))
                  (succ (+ m k)))
          :by ((eq/eq-cong int int succ (+ k m) (+ m k)) Hind))
    (have <b3> (= (+ (succ k) m)
                  (succ (+ m k))) :by (eq/eq-trans% <b1> <b2>))
    (have <b4> (= (succ (+ m k))
                  (+ m (succ k))) :by (eq/eq-sym% (plus-succ m k)))
    (have <b> (P (succ k)) :by (eq/eq-trans% <b3> <b4>))
    "Second the predecessor case, we show `(P (pred k))`."
    (have <c1> (= (+ (pred k) m)
                  (pred (+ k m))) :by (plus-pred-sym k m))
    (have <c2> (= (pred (+ k m))
                  (pred (+ m k)))
          :by ((eq/eq-cong int int pred (+ k m) (+ m k)) Hind))
    (have <c3> (= (+ (pred k) m)
                  (pred (+ m k))) :by (eq/eq-trans% <c1> <c2>))
    (have <c4> (= (pred (+ m k))
                  (+ m (pred k))) :by (eq/eq-sym% (plus-pred m k)))
    (have <c> (P (pred k)) :by (eq/eq-trans% <c3> <c4>))
    (have <d> _ :by (p/and-intro% <b> <c>)))
  "Now we apply integer induction."
  (have <e> (P n) :by ((int/int-induct P) <a> <d> n))
  (qed <e>))

(defthm plus-pred-succ
  [[n int] [m int]]
  (= (+ (pred n) (succ m))
     (+ n m)))

(proof plus-pred-succ
    :script
  (have <a> (= (+ (pred n) (succ m))
               (pred (+ n (succ m))))
        :by (plus-pred-sym n (succ m)))
  (have <b> (= (+ n (succ m))
               (succ (+ n m))) :by (plus-succ n m))
  (have <c> (= (+ (pred n) (succ m))
               (pred (succ (+ n m))))
        :by (eq/eq-subst%
             (lambda [k int]
               (= (+ (pred n) (succ m))
                  (pred k)))
             <b> <a>))
  (have <d> (= (pred (succ (+ n m)))
               (+ n m))
        :by (int/pred-of-succ (+ n m)))
  (have <e> (= (+ (pred n) (succ m))
               (+ n m)) :by (eq/eq-trans% <c> <d>))
  (qed <e>))

(defthm plus-succ-pred
  [[n int] [m int]]
  (= (+ (succ n) (pred m))
     (+ n m)))

(proof plus-succ-pred
    :script
  (have <a> (= (+ (succ n) (pred m))
               (+ (pred m) (succ n)))
        :by (plus-commute (succ n) (pred m)))
  (have <b> (= (+ (pred m) (succ n))
               (+ m n)) :by (plus-pred-succ m n))
  (have <c> (= (+ (succ n) (pred m))
               (+ m n)) :by (eq/eq-trans% <a> <b>))
  (have <d> (= (+ m n) (+ n m))
        :by (plus-commute m n))
  (have <e> (= (+ (succ n) (pred m))
               (+ n m)) :by (eq/eq-trans% <c> <d>))
  (qed <e>))

(defthm plus-assoc
  [[n int] [m int] [p int]]
  (= (+ n (+ m p))
     (+ (+ n m) p)))

(proof plus-assoc
    :script
  (have P _ :by (lambda [k int]
                  (= (+ n (+ m k))
                     (+ (+ n m) k))))
  "We prove `P` by induction on `k`."
  "First `(P zero)`"
  (have <a1> (= (+ n (+ m zero))
                (+ n m))
        :by (eq/eq-cong% (lambda [k int] (+ n k))
                         (plus-zero m)))
  (have <a2> (= (+ n m)
                (+ (+ n m) zero))
        :by (eq/eq-sym% (plus-zero (+ n m))))
  (have <a> (P zero) :by (eq/eq-trans% <a1> <a2>))
  "Then the inductive cases."
  (assume [p int
           Hind (= (+ n (+ m p))
                   (+ (+ n m) p))]
    "Let's prove `(P (succ p))`."
    (have <b1> (= (+ n (+ m (succ p)))
                  (+ n (succ (+ m p))))
          :by (eq/eq-cong% (lambda [k int] (+ n k))
                           (plus-succ m p)))
    (have <b2>  (= (+ n (succ (+ m p)))
                   (succ (+ n (+ m p))))
          :by (plus-succ n (+ m p)))
    (have <b3> (= (+ n (+ m (succ p)))
                  (succ (+ n (+ m p))))
          :by (eq/eq-trans% <b1> <b2>))
    (have <b4> (= (succ (+ n (+ m p)))
                  (succ (+ (+ n m) p)))
          :by (eq/eq-cong% succ Hind))
    (have <b5> (= (+ n (+ m (succ p)))
                  (succ (+ (+ n m) p)))
          :by (eq/eq-trans% <b3> <b4>))
    ;; = (+ (+ n m) (succ p))
    (have <b6> (= (succ (+ (+ n m) p))
                  (+ (+ n m) (succ p)))
          :by (eq/eq-sym% (plus-succ (+ n m) p)))
    (have <b> (P (succ p))
          :by (eq/eq-trans% <b5> <b6>))
    "and next prove `(P (pred p))`."
    (have <c1> (= (+ n (+ m (pred p)))
                  (+ n (pred (+ m p))))
          :by (eq/eq-cong% (lambda [k int] (+ n k))
                           (plus-pred m p)))
    (have <c2> (= (+ n (pred (+ m p)))
                  (pred (+ n (+ m p))))
          :by (plus-pred n (+ m p)))
    (have <c3> (= (+ n (+ m (pred p)))
                  (pred (+ n (+ m p))))
          :by (eq/eq-trans% <c1> <c2>))
    (have <c4> (= (pred (+ n (+ m p)))
                  (pred (+ (+ n m) p)))
          :by (eq/eq-cong% pred Hind))
    (have <c5> (= (+ n (+ m (pred p)))
                   (pred (+ (+ n m) p)))
           :by (eq/eq-trans% <c3> <c4>))
    ;; = (+ (+ n m) (pred p))
    (have <c6> (= (pred (+ (+ n m) p))
                  (+ (+ n m) (pred p)))
          :by (eq/eq-sym% (plus-pred (+ n m) p)))
    (have <c> (P (pred p)) :by (eq/eq-trans% <c5> <c6>))
    (have <d> _ :by (p/and-intro% <b> <c>)))
  "Now we apply the integer induction."
  (have <e> (P p) :by ((int/int-induct P) <a> <d> p))
  (qed <e>))

(defthm plus-right-cancel
  [[n int] [m int] [p int]]
  (==> (= (+ n p) (+ m p))
       (= n m)))

(proof plus-right-cancel
    :script
  "We proceed by induction."
  "Base case."
  (assume [Hz (= (+ n zero) (+ m zero))]
    (have <a1> (= n (+ m zero))
          :by (eq/eq-subst% (lambda [k int] (= k (+ m zero)))
                            (plus-zero n)
                            Hz))
    (have <a> (= n m)
          :by (eq/eq-subst% (lambda [k int] (= n k))
                            (plus-zero m)
                            <a1>)))
  "Inductive cases."
  (assume [k int
           Hk (==> (= (+ n k) (+ m k))
                   (= n m))]
    "Successor case."
    (assume [Hsucc (= (+ n (succ k)) (+ m (succ k)))]
      (have <b1> (= (succ (+ n k)) (+ m (succ k)))
            :by (eq/eq-subst% (lambda [i int] (= i (+ m (succ k))))
                              (plus-succ n k)
                              Hsucc))
      (have <b2> (= (succ (+ n k)) (succ (+ m k)))
            :by (eq/eq-subst% (lambda [i int] (= (succ (+ n k)) i))
                              (plus-succ m k)
                              <b1>))
      (have <b3> (= (+ n k) (+ m k)) :by (int/succ-injective (+ n k) (+ m k) <b2>))
      (have <b> (= n m) :by (Hk <b3>)))
    "Predecessor case."
    (assume [Hpred (= (+ n (pred k)) (+ m (pred k)))]
      (have <c1> (= (pred (+ n k)) (+ m (pred k)))
            :by (eq/eq-subst% (lambda [i int] (= i (+ m (pred k))))
                              (plus-pred n k)
                              Hpred))
      (have <c2> (= (pred (+ n k)) (pred (+ m k)))
            :by (eq/eq-subst% (lambda [i int] (= (pred (+ n k)) i))
                              (plus-pred m k)
                              <c1>))
      (have <c3> (= (+ n k) (+ m k))
            :by (int/pred-injective (+ n k) (+ m k) <c2>))
      (have <c> (= n m) :by (Hk <c3>)))
    (have <d> _ :by (p/and-intro% <b> <c>)))
  "We apply the induction principle."
  (have <e> _ :by ((int/int-induct (lambda [k int]
                                     (==> (= (+ n k) (+ m k))
                                          (= n m)))) <a> <d> p))
  (qed <e>))

(defthm plus-left-cancel
  [[n int] [m int] [p int]]
  (==>  (= (+ p n) (+ p m))
        (= n m)))

(proof plus-left-cancel
    :script
  (assume [H (= (+ p n) (+ p m))]
    (have <a> (= (+ n p) (+ p m))
          :by (eq/eq-subst% (lambda [k int] (= k (+ p m)))
                            (plus-commute p n)
                            H))
    (have <b> (= (+ n p) (+ m p))
          :by (eq/eq-subst% (lambda [k int] (= (+ n p) k))
                            (plus-commute p m)
                            <a>))
    (have <c> (= n m) :by ((plus-right-cancel n m p) <b>)))
  (qed <c>))

(defthm plus-right-cancel-conv
  [[n int] [m int] [p int]]
  (==> (= n m)
       (= (+ n p) (+ m p))))

(proof plus-right-cancel-conv
    :script
  (assume [H (= n m)]
    (have <a> (= (+ n p) (+ m p))
          :by (eq/eq-cong% (lambda [k int] (+ k p))
                           H)))
  (qed <a>))

(defthm plus-left-cancel-conv
  [[n int] [m int] [p int]]
  (==> (= n m)
       (= (+ p n) (+ p m))))

(proof plus-left-cancel-conv
    :script
  (assume [H (= n m)]
    (have <a> (= (+ p n) (+ p m))
          :by (eq/eq-cong% (lambda [k int] (+ p k))
                           H)))
  (qed <a>))


(defthm plus-nat-closed
  "The addition is closed for natural integers."
  []
  (forall-in [n int nat]
    (forall-in [m int nat]
      (elem int (+ n m) nat))))

(proof plus-nat-closed
    :script
  (assume [n int
           Hn (elem int n nat)]
    (have P _ :by (lambda [m int]
                    (elem int (+ n m) nat)))
    "We prove `P` by natural induction."
    "First let's prove `(P zero)`."
    (have <a> (P zero)
          :by ((eq/eq-subst int
                            (lambda [k int]
                              (elem int k nat))
                            n
                            (+ n zero))
               (eq/eq-sym% (plus-zero n))
               Hn))
    "Then the inductive case."
    (assume [k int
             Hk (elem int k nat)
             Hind (elem int (+ n k) nat)]
      ;; proove: (elem int (+ n (succ k) nat))
      (have <b1> (elem int (succ (+ n k)) nat)
            :by ((nat/nat-succ (+ n k)) Hind))
      (have <b> (P (succ k))
            :by ((eq/eq-subst int
                              (lambda [i int] (elem int i nat))
                              (succ (+ n k))
                              (+ n (succ k)))
                 (eq/eq-sym% (plus-succ n k))
                 <b1>)))
    "And finally we apply the induction principle."
    (have <c> (forall-in [m int nat]
                (elem int (+ n m) nat))
          :by ((nat/nat-induct P) <a> <b>)))
  (qed <c>))


(defthm negative-plus
  []
  (forall [n int]
    (==> (nat/negative n)
         (exists [m int]
           (and (nat/positive m)
                (= (+ n m) zero))))))

;; (proof negative-plus
;;     :script
;;   "We prove this by integer induction."
;;   "Base case: `zero`"
;;   (assume [Hcontra (negative zero)]
;;     "We proceed by contradiction."
;;     (have <a1> p/absurd :by (Hcontra (nat/nat-zero)))
;;     (have <a> _
;;           :by (<a1> (exists [m int]
;;                       (and (positive m)
;;                            (= (+ n m) zero))))))
;;   "Inductive cases."
;;   (assume [n int
;;            Hind (==> (nat/negative n)
;;                      (exists [m int]
;;                        (and (positive m)
;;                             (= (+ n m) zero))))]
;;     "First, let's show the case for `(succ n)`."
;;     (assume [Hsucc (negative (succ n))]
;;       (have <b1> (negative (pred (succ n)))
;;             :by ((nat/negative-pred (succ n))
;;                  Hsucc))
;;       (have <b2> (negative n)
;;             :by (eq/eq-subst% negative
;;                               (int/pred-of-succ n)
;;                               <b1>))
;;       (have <b3> (exists [m int]
;;                    (and (positive m)
;;                         (= (+ n m) zero)))
;;             :by (Hind <b2>))
;;       (assume [m int
;;                Hm (and (positive m)
;;                        (= (+ n m) zero))]
;;         (have <b4> (or (= (pred m) zero)
;;                        (positive (pred m)))
;;               :by (nat/nat-split (pred m) (p/and-elim-left% Hm)))
;;         (assume [Hmz (= (pred m) zero)]
;;           (have <c1> (= (succ (pred m)) (succ zero))
;;                 :by (eq/eq-cong% succ Hmz))
;;           (have <c2> (= m (succ zero))
;;                 :by (eq/eq-subst% (lambda [k int] (= k (succ zero)))
;;                                   (int/succ-of-pred m)
;;                                   <c1>))
;;           (have <c3> (= (+ n (succ zero)) zero)
;;                 :by ))))))

