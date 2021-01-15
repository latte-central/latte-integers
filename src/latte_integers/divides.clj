(ns latte-integers.divides
  
  "The divisibility relation defined on ℤ."
  
  (:refer-clojure :exclude [and or not int = + - *])

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

            [latte-integers.int :as int :refer [zero one succ pred int =]]
            [latte-integers.nat :as nat :refer [nat positive negative]]
            [latte-integers.rec :as rec]
            [latte-integers.plus :as plus :refer [+]]
            [latte-integers.minus :as minus :refer [- --]]
            [latte-integers.times :as times :refer [*]]))

(definition divides
  "The divisibility relation.
`(divides m n)` says that `m` divides `n`."
  [[m int] [n int]]
  (exists [p int]
    (= (* m p) n)))

(defthm divides-zero
  [[n int]]
  (divides n zero))

(proof 'divides-zero
  (have <a> (= (* n zero) zero)
        :by (times/times-zero n))

  (have <b> (exists [p int]
              (= (* n p) zero))
        :by ((q/ex-intro (lambda [p int]
                           (= (* n p) zero)) zero)
             <a>))
  (qed <b>))

(defthm divides-zero-zero
  []
  (divides zero zero))

(proof 'divides-zero-zero
  (qed (divides-zero zero)))

(defthm divides-zero-conv
  [[n int]]
  (==> (divides zero n)
       (= n zero)))

(proof 'divides-zero-conv
  (assume [Hn (divides zero n)]
    (assume [p int
             Hp (= (* zero p) n)]
      (have <a> (= (* zero p) zero)
            :by (times/times-zero-swap p))
      (have <b> (= zero n)
            :by (eq/rewrite Hp <a>))
      (have <c> (= n zero) :by (eq/eq-sym <b>)))
    (have <d> (= n zero)
          :by (q/ex-elim Hn <c>)))
  (qed <d>))

(defthm divides-opp
  [[m int] [n int]]
  (==> (divides m n)
       (divides (-- m) n)))

(proof 'divides-opp
  (assume [Hnm (divides m n)]
    (assume [p int
             Hp (= (* m p) n)]

      (have <a> (= (* m p) (* (-- m) (-- p)))
            :by (eq/eq-sym (times/times-opp-opp m p)))
      (have <b> (= (* (-- m) (-- p)) n)
            :by (eq/rewrite Hp <a>))
      (have <c> (divides (-- m) n)
            :by ((q/ex-intro (lambda [k int]
                               (= (* (-- m) k) n)) (-- p))
                 <b>)))
    (have <d> _ :by (q/ex-elim Hnm <c>)))
  (qed <d>))

(defthm divides-one
  [[n int]]
  (divides one n))

(proof 'divides-one
  (have <a> (= (* one n) n)
        :by (times/times-one-swap n))
  (have <b> (divides one n)
        :by ((q/ex-intro (lambda [p int]
                           (= (* one p) n)) n)
             <a>))
  (qed <b>))

(defthm divides-refl
  [[n int]]
  (divides n n))

(proof 'divides-refl
  (have <a> (= (* n one) n)
        :by (times/times-one n))
  (have <b> _
        :by ((q/ex-intro (lambda [p int]
                           (= (* n p) n)) one)
             <a>))
  (qed <b>))

(defthm divides-trans
  [[m int] [n int] [p int]]
  (==> (divides m n)
       (divides n p)
       (divides m p)))

(proof 'divides-trans
  (assume [Hnm (divides m n)
           Hmp (divides n p)]
    (assume [a int
             Hp (= (* m a) n)]
      (assume [b int
               Hq (= (* n b) p)]
        (have <a> (= n (* m a)) :by (eq/eq-sym Hp))
        (have <b> (= (* (* m a) b) p)
              :by (eq/rewrite Hq <a>))
        (have <c> (= (* m (* a b)) p)
              :by (eq/rewrite <b> (times/times-assoc m a b)))
        (have <d> (divides m p)
              :by ((q/ex-intro (lambda [k int]
                                 (= (* m k) p)) (* a b))
                   <c>)))
      (have <e> (divides m p)
            :by (q/ex-elim Hmp <d>)))
    (have <f> (divides m p)
          :by (q/ex-elim Hnm <e>)))
  (qed <f>))

(defthm divides-nat-antisym
  "Antisymmetry of divisibility only applies to naturals."
  [[m int] [n int]]
  (==> (elem m nat)
       (elem n nat)
       (divides m n)
       (divides n m)
       (= m n)))

(proof 'divides-nat-antisym
  (assume [Hm (elem m nat)
           Hn (elem n nat)
           H1 (divides m n)
           H2 (divides n m)]
    (assume [a int
             Ha (= (* m a) n)]
      (assume [b int
               Hb (= (* n b) m)]
        ;; to show: (= m n)
        (have <a1> (= n (* m a)) :by (eq/eq-sym Ha))
        (have <a2> (= (* (* m a) b) m)
              :by (eq/rewrite Hb <a1>))

        (have <a3> (= (* m (* a b)) m)
              :by (eq/rewrite <a2> (times/times-assoc m a b)))

        (have <a4> (= (- (* m (* a b)) m) (- m m))
              :by (eq/eq-cong (lambda [k int] (- k m))
                               <a3>))

        (have <a5> (= (* m (pred (* a b))) (- m m))
              :by (eq/rewrite <a4> (times/times-pred-sym m (* a b))))

        (have <a> (= (* m (pred (* a b))) zero)
              :by (eq/rewrite <a5> (minus/minus-cancel m)))
 
        (have <b1> (= m (* n b)) :by (eq/eq-sym Hb))

        (have <b2> (= (* (* n b) a) n)
              :by (eq/rewrite Ha <b1>))

        (have <b3> (= (* n (* b a)) n)
              :by (eq/rewrite <b2> (times/times-assoc n b a)))

        (have <b4> (= (* n (* a b)) n)
              :by (eq/rewrite <b3> (times/times-commute b a)))

        (have <b5> (= (- (* n (* a b)) n) (- n n))
              :by (eq/eq-cong (lambda [k int] (- k n))
                               <b4>))

        (have <b6> (= (* n (pred (* a b))) (- n n))
              :by (eq/rewrite <b5> (times/times-pred-sym n (* a b))))

        (have <b> (= (* n (pred (* a b))) zero)
              :by (eq/rewrite <b6> (minus/minus-cancel n)))

        (have <c1> (= zero (* n (pred (* a b))))
              :by (eq/eq-sym <b>))


        (have <c> (= (* m (pred (* a b)))
                     (* n (pred (* a b))))
              :by (eq/eq-trans <a> <c1>))

        "We apply the zero-splitting principle."
        (assume [Hz (= (pred (* a b)) zero)]
          (have <d1> (= (succ (pred (* a b))) one)
                :by (eq/eq-cong succ Hz))

          (have <d2> (= (* a b) one)
                :by (eq/rewrite <d1> (int/succ-of-pred (* a b))))

          (have <d> (or (and (= a one) (= b one))
                         (and (= a (-- one)) (= b (-- one))))
                :by ((times/times-eq-one a b) <d2>))

          (assume [Hone (and (= a one) (= b one))]
            (have <e1> (= a one) :by (p/and-elim-left Hone))
            (have <e2> (= (* m one) n)
                  :by (eq/rewrite Ha <e1>))

            (have <e> (= m n)
                  :by (eq/rewrite <e2> (times/times-one m))))

          (assume [Hmone (and (= a (-- one)) (= b (-- one)))]
            (have <f1> (= a (-- one)) :by (p/and-elim-left Hmone))
            (have <f2> (= (* m (-- one)) n)
                  :by (eq/rewrite Ha <f1>))

            (have <f3> (= (-- (* m one)) n)
                  :by (eq/rewrite <f2> (times/times-opp m one)))

            (have <f4> (= (-- m) n)
                  :by (eq/rewrite <f3> (times/times-one m)))

            (have <f5> (= n (-- m)) :by (eq/eq-sym <f4>))

            (have <f> (elem (-- m) nat)
                  :by (eq/rewrite Hn <f5>))

            (have <g> (or (= (-- m) zero)
                          (positive (-- m)))
                  :by (nat/nat-split (-- m) <f>))

            (assume [Hmmz (= (-- m) zero)]
              (have <h1> (= m zero)
                    :by ((minus/zero-opp-zero-conv m) Hmmz))
              (have <h2> (= zero n)
                    :by (eq/rewrite <f4> Hmmz))

              (have <h> (= m n) :by (eq/eq-trans <h1> <h2>)))
            (assume [Hmmpos (positive (-- m))]
              (have <i1> (negative (-- (-- m)))
                    :by ((minus/opp-pos-neg (-- m)) Hmmpos))
              (have <i2> (negative m)
                    :by (eq/rewrite <i1> (minus/opp-opp m)))

              (have <i3> p/absurd :by (<i2> Hm))
              (have <i> (= m n) :by (<i3> (= m n))))

            (have <j> (= m n) :by (p/or-elim <g> <h> <i>)))

          (have <k> (= m n) :by (p/or-elim <d> <e> <j>)))

        (assume [Hnz (not (= (pred (* a b)) zero))]
          (have <l> (= m n)
                :by ((times/times-right-cancel m n (pred (* a b)))
                     <c> Hnz)))

        "No we are ready for the final elimination."
        (have <m> (or (= (pred (* a b)) zero)
                      (not (= (pred (* a b)) zero)))
              :by (nat/int-split-zero (pred (* a b))))

        (have <n> (= m n) :by (p/or-elim <m> <k> <l>)))
      "Now we eliminate the existentials."
      (have <o> (= m n) :by (q/ex-elim H2 <n>)))
    (have <p> (= m n) :by (q/ex-elim H1 <o>)))
  (qed <p>))


