(ns latte-integers.times
  "The multiplication defined on ℤ."

  (:refer-clojure :exclude [and or not int = + - *])

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
            [latte-integers.minus :as minus :refer [-]]))

(definition plus-fun
  "The addition function used in multiplication."
  [[m int]]
  (lambda [n int] (+ n m)))

(deflemma plus-fun-injective
  [[m int]]
  (fun/injective int int (plus-fun m)))

(proof plus-fun-injective
    :script
  (assume [n1 int
           n2 int
           Heq (= ((plus-fun m) n1) ((plus-fun m) n2))]
    (have <a> (= (+ n1 m) (+ n2 m)) :by Heq)
    (have <b> (= n1 n2)
          :by ((plus/plus-right-cancel n1 n2 m) <a>))
    (qed <b>)))

(deflemma plus-fun-surjective
  [[m int]]
  (fun/surjective int int (plus-fun m)))

(proof plus-fun-surjective
    :script
  (assume [n int]
    (have <a> (= ((plus-fun m) (- n m))
                 (+ (- n m) m))
          :by (eq/eq-refl int ((plus-fun m) (- n m))))
    (have <b> (= ((plus-fun m) (- n m))
                 n) :by (minus/minus-prop n m))
    (have <c> (q/ex int (lambda [x int] (= ((plus-fun m) x)
                                           n)))
          :by ((q/ex-intro int (lambda [x int] (= ((plus-fun m) x)
                                                  n)) (- n m))
               <b>))
    (qed <c>)))

(deflemma plus-fun-bijective
  [[m int]]
  (fun/bijective int int (plus-fun m)))

(proof plus-fun-bijective
    :script
  (have <a> _ :by (p/and-intro% (plus-fun-injective m)
                                (plus-fun-surjective m)))
  (qed <a>))

(definition mult-prop
  "The property of the multiplication function on integers."
  [[m int]]
  (lambda [g (==> int int)]
    (and (= (g zero) zero)
         (forall [x int]
           (= (g (succ x)) ((plus-fun m) (g x)))))))

(defthm mult-unique
  "The unicity of the multiplication function, through [[mult-prop]]."
  [[m int]]
  (q/unique (==> int int)
            (mult-prop m)))

(proof mult-unique
    :term
  (rec/int-recur-bijection int zero (plus-fun m) (plus-fun-bijective m)))

(definition times
  "The function that multiplies `m` to an integer"
  [[m int]]
  (q/the (==> int int)
         (mult-prop m)
         (mult-unique m)))

(definition *
  "The function that multiplies `m` with `n`."
  [[m int] [n int]]
  ((times m) n))

(defthm times-prop
  [[m int]]
  (and (= ((times m) zero) zero)
       (forall [n int]
         (= (* m (succ n))
            (+ (* m n) m)))))

(proof times-prop
    :term
  (q/the-prop
      (==> int int)
    (mult-prop m)
    (mult-unique m)))

(defthm times-zero
  [[n int]]
  (= (* n zero)
     zero))

(proof times-zero
    :script
  (have <a> _ :by (p/and-elim-left% (times-prop n)))
  (qed <a>))

(defthm times-succ
  [[m int] [n int]]
  (= (* m (succ n))
     (+ (* m n) m)))

(proof times-succ
    :script
  (have <a> _ :by ((p/and-elim-right% (times-prop m)) n))
  (qed <a>))

(defthm times-succ-sym
  [[m int] [n int]]
  (= (+ (* m n) m)
     (* m (succ n))))

(proof times-succ-sym
    :script
  (have <a> _ :by (eq/eq-sym% (times-succ m n)))
  (qed <a>))

(defthm times-pred
  [[m int] [n int]]
  (= (* m (pred n))
     (- (* m n) m)))

(proof times-pred
    :script
  (have <a> (= (* m (succ (pred n)))
               (+ (* m (pred n)) m))
        :by (times-succ m (pred n)))

  (have <b> (= (* m n)
               (+ (* m (pred n)) m))
        :by (eq/eq-subst% (lambda [k int] (= (* m k)
                                             (+ (* m (pred n)) m)))
                          (int/succ-of-pred n)
                          (<a>)))

  (have <c> (= (- (* m n) m)
               (- (+ (* m (pred n)) m) m))
        :by (eq/eq-cong% (lambda [k int] (- k m))
                         <b>))

  (have <d> (= (- (* m n) m)
               (* m (pred n)))
        :by (eq/eq-subst% (lambda [k int] (= (- (* m n) m)
                                             k))
                          (minus/minus-prop-cons (* m (pred n)) m)
                          <c>))
  
  (have <e> (= (* m (pred n))
               (- (* m n) m))
        :by (eq/eq-sym% <d>))

  (qed <e>))

(defthm times-pred-sym
  [[m int] [n int]]
  (= (- (* m n) m)
     (* m (pred n))))

(proof times-pred-sym
    :script
  (have <a> _ :by (eq/eq-sym% (times-pred m n)))
  (qed <a>))

(defthm times-zero-swap
  [[n int]]
  (= (* zero n)
     zero))

(proof times-zero-swap
    :script
  "This is by induction on `n`."
  (have P _ :by (lambda [k int] (= (* zero k)
                                   zero)))
  "Base case: n=0"
  (have <a> (P zero)
        :by (times-zero zero))
  "Inductive cases"
  (assume [k int
           Hind (= (* zero k)
                   zero)]
    "Successor case"
    (have <b1> (= (* zero (succ k))
                  (+ (* zero k) zero))
          :by (times-succ zero k))
    (have <b2> (= (* zero (succ k))
                  (* zero k))
          :by (eq/eq-subst% (lambda [j int] (= (* zero (succ k))
                                               j))
                            (plus/plus-zero (* zero k))
                            <b1>))
    (have <b> (P (succ k))
          :by (eq/eq-subst% (lambda [j int] (= (* zero (succ k))
                                               j))
                            Hind <b2>))
    "Predecessor case"
    (have <c1> (= (* zero (pred k))
                  (- (* zero k) zero))
          :by (times-pred zero k))
    (have <c2> (= (* zero (pred k))
                  (* zero k))
          :by (eq/eq-subst% (lambda [j int] (= (* zero (pred k))
                                               j))
                            (minus/minus-zero (* zero k))
                            <c1>))
    (have <c> (P (pred k))
          :by (eq/eq-subst% (lambda [j int] (= (* zero (pred k))
                                               j))
                            Hind <c2>))
    (have <d> (and (P (succ k))
                   (P (pred k))) :by (p/and-intro% <b> <c>)))
  "Apply the induction principle"
  (have <e> (P n) :by ((int/int-induct P)
                       <a> <d> n))
  (qed <e>))


(defthm times-succ-swap
  [[n int] [m int]]
  (= (* (succ n) m)
     (+ (* n m) m)))

(proof times-succ-swap
    :script
  "We proceed by induction on m"
  (have P _ :by (lambda [k int] (= (* (succ n) k)
                                   (+ (* n k) k))))
  "Base case n=0"
  (have <a1> (= (* (succ n) zero)
                zero)
        :by (times-zero (succ n)))
  (have <a2> (= (+ (* n zero) zero)
                (+ zero zero))
        :by (eq/eq-cong% (lambda [k int] (+ k zero))
                         (times-zero n)))
  (have <a3> (= (+ (* n zero) zero)
                zero)
        :by (eq/eq-subst% (lambda [k int] (= (+ (* n zero) zero)
                                             k))
                          (plus/plus-zero zero)
                          <a2>))
  (have <a4> (= zero
                (+ (* n zero) zero))
        :by (eq/eq-sym% <a3>))
  (have <a> (P zero) :by (eq/eq-trans% <a1> <a4>))
  "Inductive cases"
  (assume [k int
           Hind (= (* (succ n) k)
                   (+ (* n k) k))]
    "Successor case"
    (have <b1> (= (* (succ n) (succ k))
                  (+ (* (succ n) k) (succ n)))
          :by (times-succ (succ n) k))

    (have <b2> (= (+ (* (succ n) k) (succ n))
                  (+ (+ (* n k) k) (succ n)))
          :by (eq/eq-cong% (lambda [j int] (+ j (succ n)))
                           Hind))

    (have <b3> (= (+ (* (succ n) k) (succ n))
                  (succ (+ (+ (* n k) k) n)))
          :by (eq/eq-subst% (lambda [j int] (= (+ (* (succ n) k) (succ n))
                                               j))
                            (plus/plus-succ (+ (* n k) k) n)
                            <b2>))

    (have <b4> (= (+ (* (succ n) k) (succ n))
                  (succ (+ (* n k) (+ k n))))
          :by (eq/eq-subst% (lambda [j int] (= (+ (* (succ n) k) (succ n))
                                               (succ j)))
                            (plus/plus-assoc-sym (* n k) k n)
                            <b3>))

    (have <b5> (= (+ (* (succ n) k) (succ n))
                  (succ (+ (* n k) (+ n k))))
          :by (eq/eq-subst% (lambda [j int] (= (+ (* (succ n) k) (succ n))
                                               (succ (+ (* n k) j))))
                            (plus/plus-commute k n)
                            <b4>))

    (have <b6> (= (+ (* (succ n) k) (succ n))
                  (succ (+ (+ (* n k) n) k)))
          :by (eq/eq-subst% (lambda [j int] (= (+ (* (succ n) k) (succ n))
                                               (succ j)))
                            (plus/plus-assoc (* n k) n k)
                            <b5>))

    (have <b7> (= (+ (* (succ n) k) (succ n))
                  (succ (+ (* n (succ k)) k)))
          :by (eq/eq-subst% (lambda [j int] (= (+ (* (succ n) k) (succ n))
                                               (succ (+ j k))))
                            (times-succ-sym n k)
                            <b6>))

    (have <b8> (= (+ (* (succ n) k) (succ n))
                  (+ (* n (succ k)) (succ k)))
          :by (eq/eq-subst% (lambda [j int] (= (+ (* (succ n) k) (succ n))
                                               j))
                            (plus/plus-succ-sym (* n (succ k)) k)
                            <b7>))

    (have <b> (P (succ k))
      ;; (= (* (succ n) (succ k))
      ;;    (+ (* n (succ k)) (succ k)))
          :by (eq/eq-trans% <b1> <b8>))

    ;; (have P _ :by (lambda [k int] (= (* (succ n) k)
    ;;                                  (+ (* n k) k))))

    "Predecessor case"
    (have <c1> (= (* (succ n) (pred k))
                  (- (* (succ n) k) (succ n)))
          :by (times-pred (succ n) k))

    (have <c2> (= (* (succ n) (pred k))
                  (- (+ (* n k) k) (succ n)))
          :by (eq/eq-subst% (lambda [j int] (= (* (succ n) (pred k))
                                               (- j (succ n))))
                            Hind
                            <c1>))

    (have <c3> (= (* (succ n) (pred k))
                  (pred (- (+ (* n k) k) n)))
          :by (eq/eq-subst% (lambda [j int] (= (* (succ n) (pred k))
                                               j))
                            (minus/minus-succ-pred (+ (* n k) k) n)
                            <c2>))

    (have <c4> (= (* (succ n) (pred k))
                  (pred (- (+ k (* n k)) n)))
          :by (eq/eq-subst% (lambda [j int] (= (* (succ n) (pred k))
                                               (pred (- j n))))
                            (plus/plus-commute (* n k) k)
                            <c3>))

    (have <c5> (= (* (succ n) (pred k))
                  (pred (+ k (- (* n k) n))))
          :by (eq/eq-subst% (lambda [j int] (= (* (succ n) (pred k))
                                               (pred j)))
                            (minus/assoc-plus-minus-sym k (* n k) n)
                            <c4>))

    (have <c6> (= (* (succ n) (pred k))
                  (pred (+ (- (* n k) n) k)))
          :by (eq/eq-subst% (lambda [j int] (= (* (succ n) (pred k))
                                               (pred j)))
                            (plus/plus-commute k (- (* n k) n))
                            <c5>))

    (have <c7> (= (* (succ n) (pred k))
                  (+ (- (* n k) n) (pred k)))
          :by (eq/eq-subst% (lambda [j int] (= (* (succ n) (pred k))
                                               j))
                            (plus/plus-pred-sym (- (* n k) n) k)
                            <c6>))

    (have <c> (P (pred k))
      ;; (= (* (succ n) (pred k))
      ;;    (+ (* n (pred k)) (pred k)))
          :by (eq/eq-subst% (lambda [j int] (= (* (succ n) (pred k))
                                               (+ j (pred k))))
                            (times-pred-sym n k)
                            (<c7>)))

    (have <d> (and (P (succ k))
                   (P (pred k))) :by (p/and-intro% <b> <c>)))

  "We now apply the induction principle."
  (have <e> (P m) :by ((int/int-induct P) <a> <d> m))
  (qed <e>))


(defthm times-succ-swap-sym
  [[n int] [m int]]
  (= (+ (* n m) m)
     (* (succ n) m)))

(proof times-succ-swap-sym
    :script
  (have <a> _ :by (eq/eq-sym% (times-succ-swap n m)))
  (qed <a>))


(defthm times-pred-swap
  [[n int] [m int]]
  (= (* (pred n) m)
     (- (* n m) m)))

(proof times-pred-swap
    :script
  "This is by induction on `m`."
  (have P _ :by (lambda [i int]
                  (= (* (pred n) i)
                     (- (* n i) i))))
  "Base case `(P zero)`."
  (have <a1> (= (* (pred n) zero)
                zero) :by (times-zero (pred n)))
  (have <a2> (= (- (* n zero) zero)
                (* n zero)) :by (minus/minus-zero (* n zero)))
  (have <a3> (= (* n zero)
                zero) :by (times-zero n))
  (have <a4> (= (- (* n zero) zero)
                zero) :by (eq/eq-trans% <a2> <a3>))
  (have <a5> (= zero
                (- (* n zero) zero))
        :by (eq/eq-sym% <a4>))
  (have <a> (P zero) :by (eq/eq-trans% <a1> <a5>))
  "Inductive cases."
  (assume [k int
           Hind (= (* (pred n) k)
                   (- (* n k) k))]
    "Successor case."
    (have <b1> (= (* (pred n) (succ k))
                  (+ (* (pred n) k) (pred n)))
          :by (times-succ (pred n) k))
    (have <b2> (= (* (pred n) (succ k))
                  (+ (- (* n k) k) (pred n)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (succ k))
                                 (+ j (pred n))))
                            Hind <b1>))
    (have <b3> (= (* (pred n) (succ k))
                  (pred (+ (- (* n k) k) n)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (succ k))
                                 j))
                            (plus/plus-pred (- (* n k) k) n)
                            <b2>))
    (have <b4> (= (* (pred n) (succ k))
                  (pred (+ n (- (* n k) k))))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (succ k))
                                 (pred j)))
                            (plus/plus-commute (- (* n k) k) n)
                            <b3>))
    (have <b5> (= (* (pred n) (succ k))
                  (pred (- (+ n (* n k)) k)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (succ k))
                                 (pred j)))
                            (minus/assoc-plus-minus n (* n k) k )
                            <b4>))

    (have <b6> (= (* (pred n) (succ k))
                  (- (+ n (* n k)) (succ k)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (succ k))
                                 j))
                            (minus/minus-succ-pred-sym (+ n (* n k)) k)
                            <b5>))

    (have <b7> (= (* (pred n) (succ k))
                  (- (+ (* n k) n) (succ k)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (succ k))
                                 (- j (succ k))))
                            (plus/plus-commute n (* n k))
                            <b6>))

    (have <b> (P (succ k))
      ;; (= (* (pred n) (succ k))
      ;;    (- (* n (succ k)) (succ k)))
      :by (eq/eq-subst% (lambda [j int]
                          (= (* (pred n) (succ k))
                             (- j (succ k))))
                        (times-succ-sym n k)
                        <b7>))

    "Predecessor case"
    (have <c1> (= (* (pred n) (pred k))
                  (- (* (pred n) k) (pred n)))
          :by (times-pred (pred n) k))

    (have <c2> (= (* (pred n) (pred k))
                  (- (- (* n k) k) (pred n)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (pred k))
                                 (- j (pred n))))
                            Hind <c1>))

    (have <c3> (= (* (pred n) (pred k))
                  (succ (- (- (* n k) k) n)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (pred k))
                                 j))
                            (minus/minus-pred-succ (- (* n k) k) n)
                            <c2>))

    (have <c4> (= (* (pred n) (pred k))
                  (succ (- (* n k) (+ k n))))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (pred k))
                                 (succ j)))
                            (minus/assoc-minus-plus-sym (* n k) k n)
                            <c3>))

    (have <c5> (= (* (pred n) (pred k))
                  (succ (- (* n k) (+ n k))))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (pred k))
                                 (succ (- (* n k) j))))
                            (plus/plus-commute k n)
                            <c4>))

    (have <c6> (= (* (pred n) (pred k))
                  (succ (- (- (* n k) n) k)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (pred k))
                                 (succ j)))
                            (minus/assoc-minus-plus (* n k) n k)
                            <c5>))

    (have <c7> (= (* (pred n) (pred k))
                  (- (- (* n k) n) (pred k)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (pred k))
                                 j))
                            (minus/minus-pred-succ-sym (- (* n k) n) k)
                            <c6>))

    (have <c> (P (pred k))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (pred k))
                                 (- j (pred k))))
                            (times-pred-sym n k)
                            <c7>))

    (have <d> _ :by (p/and-intro% <b> <c>)))

  "We apply the induction principle."
  (have <e> (P m)
        :by ((int/int-induct (lambda [j int]
                               (= (* (pred n) j)
                                  (- (* n j) j))))
             <a> <d> m))

  (qed <e>))

(defthm times-pred-swap-sym
  [[n int] [m int]]
  (= (- (* n m) m)
     (* (pred n) m)))

(proof times-pred-swap-sym
    :script
  (have <a> _ :by (eq/eq-sym% (times-pred-swap n m)))
  (qed <a>))

(defthm times-dist-plus
  "Distributivity of multiplication over addition."
  [[n int] [m int] [p int]]
  (= (* n (+ m p))
     (+ (* n m) (* n p))))

;; The proof is quite long so we extract
;; the two inductive subcases as auxiliary lemmas.

(deflemma times-dist-plus-succ
  [[n int][m int] [p int]]
  (==> (= (* n (+ m p))
          (+ (* n m) (* n p)))
       (= (* (succ n) (+ m p))
          (+ (* (succ n) m) (* (succ n) p)))))

(proof times-dist-plus-succ
    :script
  (assume [Hind (= (* n (+ m p))
                   (+ (* n m) (* n p)))]

    (have <a> (= (* (succ n) (+ m p))
                 (+ (* n (+ m p)) (+ m p)))
          :by (times-succ-swap n (+ m p)))

    (have <b> (= (* (succ n) (+ m p))
                 (+ (+ (* n m) (* n p)) (+ m p)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (succ n) (+ m p))
                                 (+ j (+ m p))))
                            Hind <a>))

    (have <c> (= (* (succ n) (+ m p))
                 (+ (+ (* n m) (* n p)) (+ p m)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (succ n) (+ m p))
                                 (+ (+ (* n m) (* n p)) j)))
                            (plus/plus-commute m p)
                            (<b>)))

    (have <d> (= (* (succ n) (+ m p))
                 (+ (* n m) (+ (* n p) (+ p m))))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (succ n) (+ m p))
                                 j))
                            (plus/plus-assoc-sym (* n m) (* n p) (+ p m))
                            <c>))

    (have <e> (= (* (succ n) (+ m p))
                 (+ (* n m) (+ (+ (* n p) p) m)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (succ n) (+ m p))
                                 (+ (* n m) j)))
                            (plus/plus-assoc (* n p) p m)
                            <d>))

    (have <f> (= (* (succ n) (+ m p))
                 (+ (* n m) (+ m (+ (* n p) p))))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (succ n) (+ m p))
                                 (+ (* n m) j)))
                            (plus/plus-commute (+ (* n p) p) m)
                            <e>))

    (have <g> (= (* (succ n) (+ m p))
                 (+ (+ (* n m) m) (+ (* n p) p)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (succ n) (+ m p))
                                 j))
                            (plus/plus-assoc (* n m) m (+ (* n p) p))
                            <f>))

    (have <h> (= (* (succ n) (+ m p))
                 (+ (* (succ n) m) (+ (* n p) p)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (succ n) (+ m p))
                                 (+ j (+ (* n p) p))))
                            (times-succ-swap-sym n m)
                            <g>))

    ;; = (+ (* (succ n) m) (* (succ n) p)) QED
    (have <i> (= (* (succ n) (+ m p))
                 (+ (* (succ n) m) (* (succ n) p)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (succ n) (+ m p))
                                 (+ (* (succ n) m) j)))
                            (times-succ-swap-sym n p)
                            <h>))

    (qed <i>)))



(deflemma times-dist-plus-pred
  [[n int][m int] [p int]]
  (==> (= (* n (+ m p))
          (+ (* n m) (* n p)))
       (= (* (pred n) (+ m p))
          (+ (* (pred n) m) (* (pred n) p)))))

(proof times-dist-plus-pred
    :script
  (assume [Hind (= (* n (+ m p))
                   (+ (* n m) (* n p)))]

    (have <a> (= (* (pred n) (+ m p))
                 (- (* n (+ m p)) (+ m p)))
          :by (times-pred-swap n (+ m p)))

    (have <b> (= (* (pred n) (+ m p))
                 (- (+ (* n m) (* n p)) (+ m p)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (+ m p))
                                 (- j (+ m p))))
                            Hind <a>))

    (have <c> (= (* (pred n) (+ m p))
                 (+ (* n m) (- (* n p) (+ m p))))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (+ m p))
                                 j))
                            (minus/assoc-plus-minus-sym (* n m) (* n p) (+ m p))
                            <b>))

    (have <d> (= (* (pred n) (+ m p))
                 (+ (* n m) (- (* n p) (+ p m))))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (+ m p))
                                 (+ (* n m) (- (* n p) j))))
                            (plus/plus-commute m p)
                            <c>))

    (have <e> (= (* (pred n) (+ m p))
                 (+ (* n m) (- (- (* n p) p) m)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (+ m p))
                                 (+ (* n m) j)))
                            (minus/assoc-minus-plus (* n p) p m)
                            <d>))

    (have <f> (= (* (pred n) (+ m p))
                 (+ (* n m) (- (* (pred n) p) m)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (+ m p))
                                 (+ (* n m) (- j m))))
                            (times-pred-swap-sym n p)
                            <e>))

    (have <g> (= (* (pred n) (+ m p))
                 (- (+ (* n m) (* (pred n) p)) m))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (+ m p))
                                 j))
                            (minus/assoc-plus-minus (* n m) (* (pred n) p) m)
                            <f>))

    (have <h> (= (* (pred n) (+ m p))
                 (- (+ (* (pred n) p) (* n m)) m))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (+ m p))
                                 (- j m)))
                            (plus/plus-commute (* n m) (* (pred n) p))
                            <g>))

    (have <i> (= (* (pred n) (+ m p))
                 (+ (* (pred n) p) (- (* n m) m)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (+ m p))
                                 j))
                            (minus/assoc-plus-minus-sym (* (pred n) p) (* n m) m)
                            <h>))

    (have <j> (= (* (pred n) (+ m p))
                 (+ (* (pred n) p) (* (pred n) m)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (+ m p))
                                 (+ (* (pred n) p) j)))
                            (times-pred-swap-sym n m)
                            <i>))

    (have <k> (= (* (pred n) (+ m p))
                 (+ (* (pred n) m) (* (pred n) p)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (+ m p))
                                 j))
                            (plus/plus-commute (* (pred n) p) (* (pred n) m))
                            <j>))

    (qed <k>)))

(proof times-dist-plus
    :script

  (have P _ :by (lambda [k int]
                  (= (* k (+ m p))
                     (+ (* k m) (* k p)))))
  "We proceed by induction on `k`."

  "Base case: zero"
  (have <a1> (= (* zero (+ m p))
                zero)
        :by (times-zero-swap (+ m p)))
  (have <a2> (= (+ (* zero m) (* zero p))
                (+ zero (* zero p)))
        :by (eq/eq-cong% (lambda [j int]
                           (+ j (* zero p)))
                         (times-zero-swap m)))
  (have <a3> (= (+ (* zero m) (* zero p))
                (+ zero zero))
        :by (eq/eq-subst% (lambda [j int]
                            (= (+ (* zero m) (* zero p))
                               (+ zero j)))
                          (times-zero-swap p)
                          <a2>))
  (have <a4> (= (+ (* zero m) (* zero p))
                zero)
        :by (eq/eq-subst% (lambda [j int]
                            (= (+ (* zero m) (* zero p))
                               j))
                          (plus/plus-zero zero)
                          <a3>))

  (have <a5> (= zero
                (+ (* zero m) (* zero p)))
        :by (eq/eq-sym% <a4>))

  (have <a> (P zero) :by (eq/eq-trans% <a1> <a5>))

  "Inductive cases."
  (assume [k int
           Hind (= (* k (+ m p))
                   (+ (* k m) (* k p)))]
    (have <b1> (P (succ k))
          :by ((times-dist-plus-succ k m p)
               Hind))

    (have <b2> (P (pred k))
          :by ((times-dist-plus-pred k m p)
               Hind))

    (have <b> _ :by (p/and-intro% <b1> <b2>)))

  "Apply the induction principle"
  (have <c> (P n) :by ((int/int-induct (lambda [k int]
                                         (= (* k (+ m p))
                                            (+ (* k m) (* k p)))))
                       <a> <b> n))
  (qed <c>))

(defthm times-dist-minus
  "Distributivity of multiplication over subtraction."
  [[n int] [m int] [p int]]
  (= (* n (- m p))
     (- (* n m) (* n p))))

;; We extract the two complex subproofs for the inductive case.

(deflemma times-dist-minus-succ
  [[n int][m int] [p int]]
  (==> (= (* n (- m p))
          (- (* n m) (* n p)))
       (= (* (succ n) (- m p))
          (- (* (succ n) m) (* (succ n) p)))))

(proof times-dist-minus-succ
    :script
  (assume [Hind (= (* n (- m p))
                   (- (* n m) (* n p)))]

    (have <a> (= (* (succ n) (- m p))
                 (+ (* n (- m p)) (- m p)))
          :by (times-succ-swap n (- m p)))

    (have <b> (= (* (succ n) (- m p))
                 (+ (- (* n m) (* n p)) (- m p)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (succ n) (- m p))
                                 (+ j (- m p))))
                            Hind <a>))

    (have <c> (= (* (succ n) (- m p))
                 (+ (- m p) (- (* n m) (* n p))))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (succ n) (- m p))
                                 j))
                            (plus/plus-commute (- (* n m) (* n p))
                                               (- m p))
                            <b>))

    (have <d> (= (* (succ n) (- m p))
                 (- (+ (- m p) (* n m)) (* n p)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (succ n) (- m p))
                                 j))
                            (minus/assoc-plus-minus (- m p) (* n m) (* n p))
                            <c>))

    (have <e> (= (* (succ n) (- m p))
                 (- (+ (* n m) (- m p)) (* n p)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (succ n) (- m p))
                                 (- j (* n p))))
                            (plus/plus-commute (- m p) (* n m))
                            <d>))

    (have <f> (= (* (succ n) (- m p))
                 (- (- (+ (* n m) m) p) (* n p)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (succ n) (- m p))
                                 (- j (* n p))))
                            (minus/assoc-plus-minus (* n m) m p)
                            <e>))

    (have <g> (= (* (succ n) (- m p))
                 (- (- (* (succ n) m) p) (* n p)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (succ n) (- m p))
                                 (- (- j p) (* n p))))
                            (times-succ-swap-sym n m)
                            <f>))

    (have <h> (= (* (succ n) (- m p))
                 (- (* (succ n) m) (+ p (* n p))))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (succ n) (- m p))
                                 j))
                            (minus/assoc-minus-plus-sym (* (succ n) m)
                                                        p
                                                        (* n p))
                            <g>))

    (have <i> (= (* (succ n) (- m p))
                 (- (* (succ n) m) (+ (* n p) p)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (succ n) (- m p))
                                 (- (* (succ n) m) j)))
                            (plus/plus-commute p (* n p))
                            <h>))

    (have <j> (= (* (succ n) (- m p))
                 (- (* (succ n) m) (* (succ n) p)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (succ n) (- m p))
                                 (- (* (succ n) m) j)))
                            (times-succ-swap-sym n p)
                            <i>))

    (qed <j>)))


(deflemma times-dist-minus-pred
  [[n int][m int] [p int]]
  (==> (= (* n (- m p))
          (- (* n m) (* n p)))
       (= (* (pred n) (- m p))
          (- (* (pred n) m) (* (pred n) p)))))

(proof times-dist-minus-pred
    :script
  (assume [Hind (= (* n (- m p))
                   (- (* n m) (* n p)))]

    (have <a> (= (* (pred n) (- m p))
                 (- (* n (- m p)) (- m p)))
          :by (times-pred-swap n (- m p)))

    (have <b> (= (* (pred n) (- m p))
                 (- (- (* n m) (* n p)) (- m p)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (- m p))
                                 (- j (- m p))))
                            Hind <a>))

    (have <c> (= (* (pred n) (- m p))
                 (- (* n m) (+ (* n p) (- m p))))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (- m p))
                                 j))
                            (minus/assoc-minus-plus-sym (* n m)
                                                        (* n p)
                                                        (- m p))
                            <b>))

    (have <d> (= (* (pred n) (- m p))
                 (- (* n m) (+ (- m p) (* n p))))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (- m p))
                                 (- (* n m) j)))
                            (plus/plus-commute (* n p) (- m p))
                            <c>))

    (have <e> (= (* (pred n) (- m p))
                 (- (* n m) (- m (- p (* n p)))))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (- m p))
                                 (- (* n m) j)))
                            (minus/assoc-minus-minus-sym m p (* n p))
                            <d>))

    (have <f> (= (* (pred n) (- m p))
                 (+ (- (* n m) m) (- p (* n p))))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (- m p))
                                 j))
                            (minus/assoc-minus-minus (* n m) m
                                                     (- p (* n p)))
                            <e>))

    (have <g> (= (* (pred n) (- m p))
                 (- (+ (- (* n m) m) p) (* n p)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (- m p))
                                 j))
                            (minus/assoc-plus-minus (- (* n m) m)
                                                    p
                                                    (* n p))
                            <f>))

    (have <h> (= (* (pred n) (- m p))
                 (- (+ p (- (* n m) m)) (* n p)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (- m p))
                                 (- j (* n p))))
                            (plus/plus-commute (- (* n m) m) p)
                            <g>))

    (have <i> (= (* (pred n) (- m p))
                 (+ p (- (- (* n m) m) (* n p))))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (- m p))
                                 j))
                            (minus/assoc-plus-minus-sym p
                                                        (- (* n m) m)
                                                        (* n p))
                            <h>))

    (have <j> (= (* (pred n) (- m p))
                 (+ (- (- (* n m) m) (* n p)) p))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (- m p))
                                 j))
                            (plus/plus-commute
                             p
                             (- (- (* n m) m) (* n p)))
                            <i>))

    (have <k> (= (* (pred n) (- m p))
                 (- (- (* n m) m) (- (* n p) p)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (- m p))
                                 j))
                            (minus/assoc-minus-minus-sym (- (* n m) m)
                                                         (* n p)
                                                         p)
                            <j>))

    (have <l> (= (* (pred n) (- m p))
                 (- (* (pred n) m) (- (* n p) p)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (- m p))
                                 (- j (- (* n p) p))))
                            (times-pred-swap-sym n m)
                            <k>))

    (have <m> (= (* (pred n) (- m p))
                 (- (* (pred n) m) (* (pred n) p)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred n) (- m p))
                                 (- (* (pred n) m) j)))
                            (times-pred-swap-sym n p)
                            <l>))

    (qed <m>)))

(proof times-dist-minus
    :script

  (have P _ :by (lambda [k int]
                  (= (* k (- m p))
                     (- (* k m) (* k p)))))
  "We proceed by induction on `k`."

  "Base case: zero"
  (have <a1> (= (* zero (- m p))
                zero)
        :by (times-zero-swap (- m p)))
  (have <a2> (= (- (* zero m) (* zero p))
                (- zero (* zero p)))
        :by (eq/eq-cong% (lambda [j int]
                           (- j (* zero p)))
                         (times-zero-swap m)))
  (have <a3> (= (- (* zero m) (* zero p))
                (- zero zero))
        :by (eq/eq-subst% (lambda [j int]
                            (= (- (* zero m) (* zero p))
                               (- zero j)))
                          (times-zero-swap p)
                          <a2>))
  (have <a4> (= (- (* zero m) (* zero p))
                zero)
        :by (eq/eq-subst% (lambda [j int]
                            (= (- (* zero m) (* zero p))
                               j))
                          (minus/minus-zero zero)
                          <a3>))
  (have <a5> (= zero
                (- (* zero m) (* zero p)))
        :by (eq/eq-sym% <a4>))

  (have <a> (P zero) :by (eq/eq-trans% <a1> <a5>))

  "Inductive cases."
  (assume [k int
           Hind (= (* k (- m p))
                   (- (* k m) (* k p)))]
    (have <b1> (P (succ k))
          :by ((times-dist-minus-succ k m p)
               Hind))

    (have <b2> (P (pred k))
          :by ((times-dist-minus-pred k m p)
               Hind))

    (have <b> _ :by (p/and-intro% <b1> <b2>)))

  "Apply the induction principle"
  (have <c> (P n) :by ((int/int-induct (lambda [k int]
                                         (= (* k (- m p))
                                            (- (* k m) (* k p)))))
                       <a> <b> n))
  (qed <c>))


