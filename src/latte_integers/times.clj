(ns latte-integers.times
  
  "The multiplication defined on ℤ."

  (:refer-clojure :exclude [and or not int = + - * < <= > >=])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          pose try-proof ==>]]

            [latte.prop :as p :refer [and or not <=>]]
            [latte.equal :as eq :refer [equal]]
            [latte.quant :as q :refer [exists]]
            [latte.fun :as fun]

            [latte-sets.core :as set :refer [elem forall-in]]

            [latte-integers.core :as int :refer [zero one succ pred int =]]
            [latte-integers.nat :as nat :refer [nat positive negative]]
            [latte-integers.rec :as rec]
            [latte-integers.plus :as plus :refer [+]]
            [latte-integers.minus :as minus :refer [- --]]
            [latte-integers.ord :as ord :refer [< <= > >=]]))

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
  (pose P := (lambda [k int] (= (* zero k)
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
  (pose P := (lambda [k int] (= (* (succ n) k)
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
  (pose P := (lambda [i int]
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

  (pose P := (lambda [k int]
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

(defthm times-dist-plus-sym
  "The symmetric of [[times-dist-plus]]."
  [[n int] [m int] [p int]]
  (= (+ (* n m) (* n p))
     (* n (+ m p))))

(proof times-dist-plus-sym
    :script
  (have <a> _ :by (eq/eq-sym% (times-dist-plus n m p)))
  (qed <a>))

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

  (pose P := (lambda [k int]
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

(defthm times-dist-minus-sym
  "The symmetric of [[times-dist-minus]]."
  [[n int] [m int] [p int]]
  (= (- (* n m) (* n p))
     (* n (- m p))))

(proof times-dist-minus-sym
    :script
  (have <a> _ :by (eq/eq-sym% (times-dist-minus n m p)))
  (qed <a>))

(defthm times-commute
  "Commutativity of multiplication."
  [[n int] [m int]]
  (= (* n m) (* m n)))

(proof times-commute
    :script
  "By induction on `n`."
  (pose P := (lambda [k int] (= (* k m) (* m k))))
  "Base case."
  (have <a1> (= (* zero m) zero)
        :by (times-zero-swap m))
  (have <a2> (= zero (* m zero))
        :by (eq/eq-sym% (times-zero m)))
  (have <a> (P zero) :by (eq/eq-trans% <a1> <a2>))
  "Inductive cases."
  (assume [k int
           Hind (= (* k m) (* m k))]
    "Successor case."
    (have <b1> (= (* (succ k) m)
                  (+ (* k m) m))
          :by (times-succ-swap k m))
    (have <b2> (= (* (succ k) m)
                  (+ (* m k) m))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (succ k) m)
                                 (+ j m)))
                            Hind <b1>))
    (have <b> (P (succ k))
          ;;(= (* (succ k) m)
          ;;   (* m (succ k)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (succ k) m)
                                 j))
                            (times-succ-sym m k)
                            <b2>))
    "Predecessor case."
    (have <c1> (= (* (pred k) m)
                  (- (* k m) m))
          :by (times-pred-swap k m))
    (have <c2> (= (* (pred k) m)
                  (- (* m k) m))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred k) m)
                                 (- j m)))
                            Hind <c1>))
    (have <c> (P (pred k))
          ;;(= (* (succ k) m)
          ;;   (* m (succ k)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (pred k) m)
                                 j))
                            (times-pred-sym m k)
                            <c2>))

    (have <d> _ :by (p/and-intro% <b> <c>)))

  "We apply the inductive principle."
  (have <e> (P n) :by ((int/int-induct (lambda [k int]
                                         (= (* k m) (* m k))))
                       <a> <d> n))
  (qed <e>))


(defthm times-assoc
  "Associativity of multiplication."
  [[n int] [m int] [p int]]
  (= (* (* n m) p)
     (* n (* m p))))

(proof times-assoc
    :script
  "By induction on `p`."
  (pose P := (lambda [k int]
               (= (* (* n m) k)
                  (* n (* m k)))))
  "Base case"
  (have <a1> (= (* (* n m) zero)
                zero)
        :by (times-zero (* n m)))
  (have <a2> (= (* n (* m zero))
                (* n zero))
        :by (eq/eq-cong% (lambda [j int] (* n j))
                         (times-zero m)))
  (have <a3> (= (* n (* m zero))
                zero)
        :by (eq/eq-subst% (lambda [j int]
                            (= (* n (* m zero))
                               j))
                          (times-zero n)
                          <a2>))
  (have <a4> (= zero
               (* n (* m zero)))
        :by (eq/eq-sym% <a3>))

  (have <a> (P zero) :by (eq/eq-trans% <a1> <a4>))

  "Inductive cases."
  (assume [k int
           Hind (= (* (* n m) k)
                   (* n (* m k)))]

    "Successor case."

    (have <b1> (= (* (* n m) (succ k))
                  (+ (* (* n m) k) (* n m)))
          :by (times-succ (* n m) k))

    (have <b2> (= (* (* n m) (succ k))
                  (+ (* n (* m k)) (* n m)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (* n m) (succ k))
                                 (+ j (* n m))))
                            Hind <b1>))

    (have <b3> (= (* (* n m) (succ k))
                  (* n (+ (* m k) m)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (* n m) (succ k))
                                 j))
                            (times-dist-plus-sym n (* m k) m)
                            <b2>))

    (have <b> (P (succ k))
      ;; (= (* (* n m) (succ k))
      ;;    (* n (* m (succ k))))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (* n m) (succ k))
                                 (* n j)))
                            (times-succ-sym m k)
                            <b3>))

    "Predecessor case."

    (have <c1> (= (* (* n m) (pred k))
                  (- (* (* n m) k) (* n m)))
          :by (times-pred (* n m) k))

    (have <c2> (= (* (* n m) (pred k))
                  (- (* n (* m k)) (* n m)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (* n m) (pred k))
                                 (- j (* n m))))
                            Hind <c1>))

    (have <c3> (= (* (* n m) (pred k))
                  (* n (- (* m k) m)))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (* n m) (pred k))
                                 j))
                            (times-dist-minus-sym n (* m k) m)
                            <c2>))

    (have <c> (P (pred k))
      ;; (= (* (* n m) (pred k))
      ;;    (* n (* m (pred k))))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* (* n m) (pred k))
                                 (* n j)))
                            (times-pred-sym m k)
                            <c3>))

    (have <d> _ :by (p/and-intro% <b> <c>)))

  "We apply the inductive principle."

  (have <e> (P p) :by ((int/int-induct (lambda [k int]
                                         (= (* (* n m) k)
                                            (* n (* m k)))))
                       <a> <d> p))
  (qed <e>))

(defthm times-assoc-sym
  "The symmetric of [[times-assoc]]."
  [[n int] [m int] [p int]]
  (= (* n (* m p))
     (* (* n m) p)))

(proof times-assoc-sym
    :script
  (have <a> _ :by (eq/eq-sym% (times-assoc n m p)))
  (qed <a>))

(defthm times-one
  [[n int]]
  (= (* n one) n))

(proof times-one
    :script
  (have <a> (= (* n one) (+ (* n zero) n))
        :by (times-succ n zero))
  (have <b> (= (+ (* n zero) n)
               (+ zero n))
        :by (eq/eq-cong% (lambda [k int]
                           (+ k n))
                         (times-zero n)))
  (have <c> (= (+ zero n) n)
        :by (plus/plus-zero-swap n))
  (have <d> (= (* n one) n)
        :by (eq/eq-trans* <a> <b> <c>))
  (qed <d>))

(defthm times-one-swap
  [[n int]]
  (= (* one n) n))

(proof times-one-swap
    :script
  (have <a> (= (* one n) (* n one))
        :by (times-commute one n))
  (have <b> (= (* n one) n)
        :by (times-one n))
  (have <c> _ :by (eq/eq-trans% <a> <b>))
  (qed <c>))

(defthm times-opp
  [[m int] [n int]]
  (= (* m (-- n))
     (-- (* m n))))

(proof times-opp
    :script
  (have <a> (= (+ (* m (-- n)) (* m n))
               (* m (+ (-- n) n)))
        :by (times-dist-plus-sym m (-- n) n))

  (have <b> (= (+ (-- n) n) zero)
        :by (minus/opp-plus-opp n))

  (have <c> (= (+ (* m (-- n)) (* m n))
               (* m zero))
        :by (eq/eq-subst% (lambda [k int]
                            (= (+ (* m (-- n)) (* m n))
                               (* m k)))
                          <b> <a>))
  (have <d> (= (+ (* m (-- n)) (* m n))
               zero)
        :by (eq/eq-subst% (lambda [k int]
                            (= (+ (* m (-- n)) (* m n))
                               k))
                          (times-zero m)
                          <c>))

  (have <e> (= zero
               (+ (-- (* m n)) (* m n)))
        :by (eq/eq-sym% (minus/opp-plus-opp (* m n))))

  (have <f> (= (+ (* m (-- n)) (* m n))
               (+ (-- (* m n)) (* m n)))
        :by (eq/eq-trans% <d> <e>))

  (have <g> (= (* m (-- n))
               (-- (* m n)))
        :by ((plus/plus-right-cancel (* m (-- n))
                                     (-- (* m n))
                                     (* m n))
             <f>))
  (qed <g>))

(defthm times-opp-opp
  [[m int] [n int]]
  (= (* (-- m) (-- n))
     (* m n)))

(proof times-opp-opp
    :script
  (have <a> (= (* (-- m) (-- n))
               (-- (* (-- m) n)))
        :by (times-opp (-- m) n))
  (have <b> (= (* (-- m) (-- n))
               (-- (* n (-- m))))
        :by (eq/eq-subst% (lambda [k int]
                            (= (* (-- m) (-- n))
                               (-- k)))
                          (times-commute (-- m) n)
                          <a>))
  (have <c> (= (* (-- m) (-- n))
               (-- (--  (* n m))))
        :by (eq/eq-subst% (lambda [k int]
                            (= (* (-- m) (-- n))
                               (-- k)))
                          (times-opp n m)
                          <b>))

  (have <d> (= (* (-- m) (-- n))
               (* n m))
        :by (eq/eq-subst% (lambda [k int]
                            (= (* (-- m) (-- n))
                               k))
                          (minus/opp-opp (* n m))
                          <c>))

  (have <e> (= (* (-- m) (-- n))
               (* m n))
        :by (eq/eq-subst% (lambda [k int]
                            (= (* (-- m) (-- n))
                               k))
                          (times-commute n m)
                          <d>))
  (qed <e>))


(defthm times-nat-closed
  "The multiplication is closed for natural integers."
  []
  (forall-in [n int nat]
    (forall-in [m int nat]
      (elem int (* n m) nat))))

(proof times-nat-closed
    :script
  (assume [n int
           Hn (elem int n nat)]
    (pose P := (lambda [k int]
                 (elem int (* n k) nat)))
    "We prove `P` by induction on naturals."
    
    "Base case"
    
    (have <a1> (= zero (* n zero))
          :by (eq/eq-sym% (times-zero n)))
    
    (have <a> (P zero)
          ;;(elem int (* n zero) nat)
          :by (eq/eq-subst% (lambda [j int]
                              (elem int j nat))
                            <a1>
                            (nat/nat-zero)))
    
    "Inductive case"
    (assume [k int
             Hk (elem int k nat)
             Hind (elem int (* n k) nat)]
      
      (have <b1> (= (+ (* n k) n)
                    (* n (succ k)))
            :by (eq/eq-sym% (times-succ n k)))
      
      (have <b2> (elem int (+ (* n k) n) nat)
            :by (plus/plus-nat-closed
                 (* n k) Hind
                 n Hn))
      
      (have <b> (P (succ k))
            ;; (elem int (* n (succ m)) nat)
            :by (eq/eq-subst% (lambda [j int]
                                (elem int j nat))
                              <b1> <b2>))) 

    
    (have <c> (forall-in [m int nat]
                (elem int (* n m) nat))
          :by ((nat/nat-induct P) <a> <b>)))

  (qed <c>))


(defthm times-pos-pos
  [[m int] [n int]]
  (==> (positive m)
       (positive n)
       (positive (* m n))))

(proof times-pos-pos
    :script
  (assume [Hm (positive m)
           Hn (positive n)]
    ;; to prove
    ;; (elem int (pred (* m n)) nat)
    (have <a> (= (* m (succ (pred n)))
                 (* m n))
          :by (eq/eq-cong% (lambda [j int]
                             (* m j))
                           (int/succ-of-pred n)))
    (have <b> _ :by (eq/eq-sym% <a>))
    (have <c1> (= (* m n)
                 (+ (* m (pred n)) m))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* m n)
                                 j))
                            (times-succ m (pred n))
                            <b>))
    (have <c2> (= (* m n)
                 (+ m (* m (pred n))))
          :by (eq/eq-subst% (lambda [j int]
                              (= (* m n)
                                 j))
                            (plus/plus-commute (* m (pred n)) m)
                            <c1>))

    (have <c> (= (+ m (* m (pred n)))
                 (* m n))
          :by (eq/eq-sym% <c2>))
    
    (have <d> (> m zero)
          :by ((ord/pos-gt-zero m) Hm))

    (have <e1> (> (+ m (* m (pred n)))
                  (+ zero (* m (pred n))))
          :by ((ord/plus-lt-conv zero m (* m (pred n)))
               <d>))

    (have <e> (> (+ m (* m (pred n)))
                 (* m (pred n)))
          :by (eq/eq-subst% (lambda [j int]
                              (> (+ m (* m (pred n)))
                                 j))
                            (plus/plus-zero-swap (* m (pred n)))
                            <e1>))

    (have <f> (> (* m n)
                 (* m (pred n))) ;; separate thm ?
          :by (eq/eq-subst% (lambda [j int]
                              (> j (* m (pred n))))
                            <c> <e>))

    (have <g> (elem int m nat)
          :by ((nat/positive-conv m) Hm))

    (have <h> (elem int (* m (pred n)) nat)
          :by (times-nat-closed m <g>
                                (pred n) Hn))

    (have <i> (>= (* m (pred n)) zero)
          :by ((ord/nat-ge-zero (* m (pred n))) <h>))

    (have <j> (> (* m n) zero)
          :by ((ord/lt-trans-weak zero (* m (pred n)) (* m n))
               <i> <f>))

    (have <k> (positive (* m n))
          :by ((ord/pos-gt-zero-conv (* m n)) <j>))

    (qed <k>)))

(defthm times-pos-neg
  [[m int] [n int]]
  (==> (positive m)
       (negative n)
       (negative (* m n))))

(proof times-pos-neg
    :script
  (assume [Hm (positive m)
           Hn (negative n)]
    (have <a> (< n zero)
          :by ((ord/neg-lt-zero n) Hn))
    (have <b> (> (-- n) zero)
          :by ((ord/lt-zero-opp n) <a>))
    (have <c> (positive (-- n))
          :by ((ord/pos-gt-zero-conv (-- n)) <b>))
    (have <d> (> (* m (-- n)) zero)
          :by ((ord/pos-gt-zero (* m (-- n)))
               ((times-pos-pos m (-- n)) Hm <c>)))
    (have <e> (> (-- (* m n)) zero)
          :by (eq/eq-subst% (lambda [k int] (> k zero))
                            (times-opp m n)
                            <d>))
    (have <f> (< (* m n) zero)
          :by ((ord/lt-zero-opp-conv (* m n)) <e>))

    (have <g> (negative (* m n))
          :by ((ord/neg-lt-zero-conv (* m n)) <f>))

    (qed <g>)))

(defthm times-neg-pos
  [[m int] [n int]]
  (==> (negative m)
       (positive n)
       (negative (* m n))))

(proof times-neg-pos
    :script
  (assume [Hm (negative m)
           Hn (positive n)]
    (have <a> (negative (* n m))
          :by ((times-pos-neg n m) Hn Hm))

    (have <b> (negative (* m n))
          :by (eq/eq-subst% negative
                            (times-commute n m)
                            <a>))

    (qed <b>)))

(defthm times-neg-neg
  [[m int] [n int]]
  (==> (negative m)
       (negative n)
       (positive (* m n))))

(proof times-neg-neg
    :script
  (assume [Hm (negative m)
           Hn (negative n)]
    (have <a> (> (-- m) zero)
          :by ((ord/lt-zero-opp m)
               ((ord/neg-lt-zero m) Hm)))
    (have <b> (positive (-- m))
          :by ((ord/pos-gt-zero-conv (-- m)) <a>))
    (have <c> (> (-- n) zero)
          :by ((ord/lt-zero-opp n)
               ((ord/neg-lt-zero n) Hn)))
    (have <d> (positive (-- n))
          :by ((ord/pos-gt-zero-conv (-- n)) <c>))
    (have <e> (positive (* (-- m) (-- n)))
          :by ((times-pos-pos (-- m) (-- n)) <b> <d>))
    (have <f> (positive (* m n))
          :by (eq/eq-subst% positive
                            (times-opp-opp m n)
                            <e>))
    (qed <f>)))


(defthm mult-split-zero
  [[m int] [n int]]
  (==> (= (* m n) zero)
       (or (= m zero)
           (= n zero))))

(proof mult-split-zero
    :script
  (assume [H (= (* m n) zero)]
    "We use the int splitting elimination principle"
    (assume [Hz (= n zero)]
      (have <a> _ :by (p/or-intro-right% (= m zero) Hz)))
    (assume [Hp (positive n)]
      (assume [Hmz (= m zero)]
        (have <b> _ :by (p/or-intro-left% Hmz (= n zero))))
      (assume [Hmp (positive m)]
        "We show a contradiction."
        (have <c1> (positive (* m n))
              :by ((times-pos-pos m n) Hmp Hp))
        (have <c2> (positive zero)
              :by (eq/eq-subst% positive H <c1>))
        (have <c3> p/absurd
              :by (nat/nat-zero-has-no-pred <c2>))
        (have <c> (or (= m zero)
                      (= n zero))
              :by (<c3> (or (= m zero)
                            (= n zero)))))
      (assume [Hmn (negative m)]
        (have <d1> (negative (* m n))
              :by ((times-neg-pos m n) Hmn Hp))
        (have <d2> (negative zero)
              :by (eq/eq-subst% negative
                                H
                                <d1>))
        (have <d3> p/absurd
              :by (<d2> nat/nat-zero))
        (have <d> (or (= m zero)
                      (= n zero))
              :by (<d3> (or (= m zero)
                            (= n zero)))))
      (have <e> (or (= m zero)
                    (= n zero))
            :by ((nat/int-split-elim (or (= m zero)
                                         (= n zero)))
                 m <b> <c> <d>)))
    (assume [Hn (negative n)]
      (assume [Hmz (= m zero)]
        (have <f> _ :by (p/or-intro-left% Hmz (= n zero))))
      (assume [Hmp (positive m)]
        (have <g1> (negative (* m n))
              :by ((times-pos-neg m n) Hmp Hn))
        (have <g2> (negative zero)
              :by (eq/eq-subst% negative
                                H
                                <g1>))
        (have <g3> p/absurd
              :by (<g2> nat/nat-zero))
        (have <g> (or (= m zero)
                      (= n zero))
              :by (<g3> (or (= m zero)
                            (= n zero)))))
      (assume [Hmn (negative m)]
        "We show a contradiction."
        (have <h1> (positive (* m n))
              :by ((times-neg-neg m n) Hmn Hn))
        (have <h2> (positive zero)
              :by (eq/eq-subst% positive H <h1>))
        (have <h3> p/absurd
              :by (nat/nat-zero-has-no-pred <h2>))
        (have <h> (or (= m zero)
                      (= n zero))
              :by (<h3> (or (= m zero)
                            (= n zero)))))
      (have <i> (or (= m zero)
                    (= n zero))
            :by ((nat/int-split-elim (or (= m zero)
                                         (= n zero)))
                 m <f> <g> <h>)))
    "We summarize all cases."
    (have <j> (or (= m zero)
                  (= n zero))
          :by ((nat/int-split-elim (or (= m zero)
                                       (= n zero)))
               n <a> <e> <i>))

    (qed <j>)))

(defthm times-right-cancel
  [[m int] [n int] [p int]]
  (==> (= (* m p) (* n p))
       (not (= p zero))
       (= m n)))

(proof times-right-cancel
    :script
    (assume [H1 (= (* m p) (* n p))
             H2 (not (= p zero))]
      (have <a> (= (- (* m p) (* m p))
                   zero)
            :by (minus/minus-cancel (* m p)))

      (have <b> (= (- (* m p) (* n p))
                   zero)
            :by (eq/eq-subst% (lambda [k int]
                                (= (- (* m p) k)
                                   zero))
                              H1
                              <a>))

      (have <c> (= (- (* p m) (* n p))
                   zero)
            :by (eq/eq-subst% (lambda [k int]
                                (= (- k (* n p))
                                   zero))
                              (times-commute m p)
                              <b>))

      (have <d> (= (- (* p m) (* p n))
                   zero)
            :by (eq/eq-subst% (lambda [k int]
                                (= (- (* p m) k)
                                   zero))
                              (times-commute n p)
                              <c>))
      (have <e> (= (* p (- m n))
                   zero)
            :by (eq/eq-subst% (lambda [k int]
                                (= k zero))
                              (times-dist-minus-sym p m n)
                              <d>))

      (have <f> (or (= p zero)
                    (= (- m n) zero))
            :by ((mult-split-zero p (- m n))
                 <e>))

      (assume [H3 (= p zero)]
        (have <g1> p/absurd :by (H2 H3))
        (have <g> (= m n) :by (<g1> (= m n))))
      (assume [H4 (= (- m n) zero)]
        (have <h> (= m n) :by ((minus/minus-zero-conv m n) H4)))

      (have <i> (= m n) :by (p/or-elim% <f> (= m n) <g> <h>))

      (qed <i>)))


(defthm times-left-cancel
  [[m int] [n int] [p int]]
  (==> (= (* p m) (* p n))
       (not (= p zero))
       (= m n)))

(proof times-left-cancel
    :script
    (assume [H1 (= (* p m) (* p n))
             H2 (not (= p zero))]
      (have <a> (= (* m p) (* p n))
            :by (eq/eq-subst% (lambda [k int]
                                (= k (* p n)))
                              (times-commute p m)
                              H1))
      (have <b> (= (* m p) (* n p))
            :by (eq/eq-subst% (lambda [k int]
                                (= (* m p) k))
                              (times-commute p n)
                              <a>))

      (have <c> (= m n)
            :by ((times-right-cancel m n p)
                 <b> H2))

      (qed <c>)))


(defthm times-le-nat
  [[m int] [n int] [p int]]
  (==> (<= m n)
       (elem int p nat)
       (<= (* m p) (* n p))))

(proof times-le-nat
    :script
  (assume [Hmn (<= m n)
           Hp (elem int p nat)]
    "We proceed by induction on `p`"
    (pose P := (lambda [k int]
                 (<= (* m k) (* n k))))
    "Base case"
    (have <a1> (<= zero zero) :by (ord/le-refl zero))
    (have <a2> (= zero (* m zero))
          :by (eq/eq-sym% (times-zero m)))
    (have <a3> (<= (* m zero) zero)
          :by (eq/eq-subst% (lambda [k int]
                              (<= k zero))
                            <a2>
                            <a1>))
    (have <a4> (= zero (* n zero))
          :by (eq/eq-sym% (times-zero n)))
    (have <a> (P zero) :by (eq/eq-subst% (lambda [k int]
                                           (<= (* m zero) k))
                                         <a4> <a3>))

    "Inductive case"
    (assume [p int
             Hp (elem int p nat)
             Hind (<= (* m p) (* n p))]
      (have <b1> (= (+ (* m p) m) (* m (succ p)))
            :by (eq/eq-sym% (times-succ m p)))
      (have <b2> (= (+ (* n p) n) (* n (succ p)))
            :by (eq/eq-sym% (times-succ n p)))
      (have <b3> (<= (+ (* m p) m) (+ (* n p) n))
            :by ((ord/plus-le-cong (* m p) m (* n p) n)
                 Hind Hmn))
      (have <b4> (<= (* m (succ p)) (+ (* n p) n))
            :by (eq/eq-subst% (lambda [k int]
                                (<= k (+ (* n p) n)))
                              <b1>
                              <b3>))
      (have <b> (P (succ p))
            :by (eq/eq-subst% (lambda [k int]
                                (<= (* m (succ p)) k))
                              <b2>
                              <b4>)))
    
    "We apply the induction principle"
    (have <c> (<= (* m p) (* n p))
          :by ((nat/nat-induct (lambda [k int]
                                 (<= (* m k) (* n k))))
               <a> <b> p Hp)))
  (qed <c>))

(defthm times-eq-one
  [[m int] [n int]]
  (==> (= (* m n) one)
       (or (and (= m one) (= n one))
           (and (= m (-- one)) (= n (-- one))))))

(deflemma not-zero-times-one
  [[m int] [n int]]
  (==> (= m zero)
       (not (= (* m n) one))))

(proof not-zero-times-one
    :script
  (assume [Hmzero (= m zero)
           Hmn (= (* m n) one)]
    (have <a> (= zero (* zero n))
          :by (eq/eq-sym% (times-zero-swap n)))
    (have <b> (= (* zero n) one)
          :by (eq/eq-subst% (lambda [k int]
                              (= (* k n) one))
                            Hmzero
                            Hmn))
    (have <c> (= zero one)
          :by (eq/eq-trans% <a> <b>))

    (have <d> p/absurd
          :by (nat/zero-is-not-one (eq/eq-sym% <c>))))
  (qed <d>))

;; (proof times-eq-one
;;     :script
;;   (assume [Hmn (= (* m n) one)]
;;     "We proceed by case analysis for `m`."
;;     (assume [Hmzero (= m zero)]
;;       (have <a1> p/absurd
;;             :by ((not-zero-times-one m n) Hmzero Hmn))
;;       (have <a> _
;;             :by (<a1> (or (and (= m one) (= n one))
;;                           (and (= m (-- one)) (= n (-- one)))))))
;;     (assume [Hmpos (positive m)]
;;       "Case analysis for `n`."
;;       (assume [Hnzero (= n zero)]
;;         (have <b1> (= (* n m) one)
;;               :by (eq/eq-subst% (lambda [k int] (= k one))
;;                                 (times-commute m n)
;;                                 Hmn))
;;         (have <b2> p/absurd
;;               :by ((not-zero-times-one n m) Hnzero <b1>))
;;         (have <b> _
;;               :by (<b2> (or (and (= m one) (= n one))
;;                             (and (= m (-- one)) (= n (-- one)))))))
;;       ;;(assume [Hnpos (positive n)])
;;       )))


;; (defthm times-eq-one
;;   [[m int] [n int]]
;;   (==> (elem int m nat)
;;        (= (* m n) one)
;;        (= m one)))

;; (proof times-eq-one
;;     :script
;;   (assume [Hm (elem int m nat)
;;            H (= (* m n) one)]
;;     (assume [Hzero (= m zero)]
;;       (have <a1> (= zero m) :by (eq/eq-sym% Hzero))
;;       (have <a2> (= (* m n) zero)
;;             :by (eq/eq-subst% (lambda [k int] (= (* k n) zero))
;;                               <a1>
;;                               (times-zero-swap n)))
;;       (have <a3> (= zero one)
;;             :by (eq/eq-subst% (lambda [k int] (= k one))
;;                               <a2> H)))
;;     ))

