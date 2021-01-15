(ns latte-integers.rec
  "The recursion theorems for ℤ."

  (:refer-clojure :exclude [and or not int =])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          pose try-proof qed]]

            [latte-prelude.prop :as p :refer [and or not <=>]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q]
            [latte-prelude.classic :as classic]
            [latte-prelude.fun :as fun]

            [latte-sets.set :as set :refer [elem]]

            [latte-integers.int :as int :refer [zero succ pred int =]]
            [latte-integers.nat :as nat :refer [positive negative]]))

(definition int-recur-prop
  "The property of the recursion principle
for integers."
  [[?T :type] [x T] [f-succ (==> T T)] [f-pred (==> T T)]]
  (lambda [g (==> int T)]
    (and (equal (g zero) x)
         (forall [y int]
           (and (==> (positive (succ y))
                     (equal (g (succ y)) (f-succ (g y))))
                (==> (negative (pred  y))
                     (equal (g (pred y)) (f-pred (g y)))))))))

(defaxiom int-recur
  "The recursion principle for integers.

cf. [[int-recur-prop]]

According to [TT&FP,p. 318], this is derivable,
 but we introduce it as an axiom since the
derivation seems rather complex."
  [[?T :type] [x T] [f-succ (==> T T)] [f-pred (==> T T)]]
  (q/unique (int-recur-prop x f-succ f-pred)))

(definition int-recur-bijection-prop
  "Property of the recursion principle for integers, for bijections.
This is a much simpler principle if the function under study
 is bijective on ℤ (e.g. addition)."
  [[?T :type] [x T] [f (==> T T)] [b (fun/bijective f)]]
  (lambda [g (==> int T)]
    (and (equal (g zero) x)
         (forall [y int]
           (equal (g (succ y)) (f (g y)))))))

(defthm int-recur-bijection
  "The recursion principle for integers, for bijections.
This is a consequence of [[int-rec]], cf. [[int-recur-bijection-prop]]."
  [[?T :type] [x T] [f (==> T T)] [b (fun/bijective f)]]
  (q/unique (int-recur-bijection-prop x f b)))

(deflemma int-recur-bijection-lemma-1
  [[T :type] [f (==> T T)] [b (fun/bijective f)] [g (==> int T)]]
  (==> (forall [y int]
               (and (==> (positive (succ y))
                         (equal (g (succ y)) (f (g y))))
              (==> (negative (pred y))
                   (equal (g (pred y)) ((fun/inverse f b) (g y))))))
       (forall [y int]
         (equal (g (succ y)) (f (g y))))))

(proof 'int-recur-bijection-lemma-1
  (pose inv-f := (fun/inverse f b))
  (assume [H (forall [y int]
                     (and (==> (positive (succ y))
                               (equal (g (succ y)) (f (g y))))
                          (==> (negative (pred y))
                               (equal (g (pred y)) (inv-f (g y))))))]
    (assume [y int]
      "We proceed by case analysis."
      "  - first case: y is positive"
      (assume [Hpos (positive y)]
        (have <a1> (positive (succ y)) :by ((nat/positive-succ-strong y) Hpos))
        (have <a> (equal (g (succ y)) (f (g y)))
              :by ((p/and-elim-left (H y)) <a1>)))
      "  - second case: y is zero"
      (assume [Hzero (= y zero)]
        (have <b1> (positive (succ zero))
              :by ((nat/positive-succ zero)
                   nat/nat-zero))
        (have <b2> (positive (succ y))
              :by (eq/rewrite <b1> (eq/eq-sym Hzero)))
        (have <b> (equal (g (succ y)) (f (g y)))
              :by ((p/and-elim-left (H y)) <b2>)))
      "we regroup the first two cases"
      (assume [Hnat (or (= y zero)
                        (positive y))]
        (have <c> (equal (g (succ y)) (f (g y)))
              :by (p/or-elim Hnat <b> <a>)))
      "  - third case: y is negative"
      (assume [Hneg (negative y)]
        (have <d1> (negative (pred (succ y)))
              :by (eq/rewrite Hneg (eq/eq-sym (int/pred-of-succ y))))
        (have <d2> (equal (g (pred (succ y))) (inv-f (g (succ y))))
              :by ((p/and-elim-right (H (succ y))) <d1>))
        (have <d3> (equal (g y) (inv-f (g (succ y))))
              :by (eq/rewrite <d2> (int/pred-of-succ y)))
        (have <d4> (equal (f (g y)) (f (inv-f (g (succ y)))))
              :by (eq/eq-cong f <d3>))
        (have <d5> (equal (f (inv-f (g (succ y)))) (g (succ y)))
              :by ((fun/inverse-prop f b)
                   (g (succ y))))
        (have <d> (equal (g (succ y)) (f (g y)))
              :by (eq/eq-sym (eq/eq-trans <d4> <d5>))))
      "We regroup the cases (or elimination)"
      (have <e> (equal (g (succ y)) (f (g y)))
            :by (p/or-elim (nat/int-split y) <c> <d>))))
  (qed <e>))

(deflemma int-recur-bijection-lemma-2
  [[T :type] [f (==> T T)] [b (fun/bijective f)] [g (==> int T)]]
  (==> (forall [y int]
               (equal (g (succ y)) (f (g y))))
       (forall [y int]
         (and (==> (positive (succ y))
                   (equal (g (succ y)) (f (g y))))
              (==> (negative (pred y))
                   (equal (g (pred y)) ((fun/inverse f b) (g y))))))))

(proof 'int-recur-bijection-lemma-2
  (pose inv-f := (fun/inverse f b))
  (assume [H (forall [y int]
               (equal (g (succ y)) (f (g y))))]
    (assume [y int]
      (assume [Hpos (positive (succ y))]
        (have <a> (equal (g (succ y)) (f (g y))) :by (H y)))
      (assume [Hneg (negative (pred y))]
        (have <b1> (equal (g (succ (pred y))) (f (g (pred y))))
              :by (H (pred y)))
        (have <b2> (equal (g y) (f (g (pred y))))
              :by (eq/rewrite <b1> (int/succ-of-pred y)))
        (have <b3> (equal (f (g (pred y))) (g y))
              :by (eq/eq-sym <b2>))
        (have <b4> (equal (inv-f (f (g (pred y)))) (inv-f (g y)))
              :by (eq/eq-cong inv-f <b3>))
        (have <b5> (equal (inv-f (f (g (pred y)))) (g (pred y)))
              :by ((fun/inverse-prop-conv f b) (g (pred y))))
        (have <b6> (equal (g (pred y)) (inv-f (f (g (pred y)))))
              :by (eq/eq-sym <b5>))
        (have <b> (equal (g (pred y)) (inv-f (g y)))
              :by (eq/eq-trans <b6> <b4>)))
      "regroup the two conjuncts."
      (have <c> _ :by (p/and-intro <a> <b>))))
  (qed <c>))

(deflemma int-recur-bijection-lemma
  [[?T :type] [f (==> T T)] [b (fun/bijective f)] [g (==> int T)]]
  (<=> (forall [y int]
         (and (==> (positive (succ y))
                   (equal (g (succ y)) (f (g y))))
              (==> (negative (pred y))
                   (equal (g (pred y)) ((fun/inverse f b) (g y))))))
       (forall [y int]
         (equal (g (succ y)) (f (g y))))))

(proof 'int-recur-bijection-lemma-lemma
  (qed (p/iff-intro (int-recur-bijection-lemma-1 T f b g)
                    (int-recur-bijection-lemma-2 T f b g))))

(deflemma int-recur-bijection-ex
  [[?T :type] [x T] [f (==> T T)] [b (fun/bijective f)]]
  (q/ex (int-recur-bijection-prop x f b)))

(proof 'int-recur-bijection-ex-lemma
  (have <ex> (q/ex (int-recur-prop x f (fun/inverse f b)))
        :by (p/and-elim-left (int-recur x f (fun/inverse f b))))
  "Our goal is to eliminate the existential."
  (assume [g (==> int T)
           Hg ((int-recur-prop x f (fun/inverse f b)) g)] 
    (have <a> ((int-recur-bijection-prop x f b) g)
          :by (p/and-intro
               (p/and-elim-left Hg)
               (((int-recur-bijection-lemma-1 T f b) g)
                (p/and-elim-right Hg))))
    (have <b> (q/ex (int-recur-bijection-prop x f b))
          :by ((q/ex-intro (int-recur-bijection-prop x f b) g)
               <a>)))
  (qed (q/ex-elim <ex> <b>)))

(deflemma int-recur-bijection-single
  [[?T :type] [x T] [f (==> T T)] [b (fun/bijective f)]]
  (q/single (int-recur-bijection-prop x f b)))

(proof 'int-recur-bijection-single-lemma
  (have <single> (forall [g h (==> int T)]
                   (==> ((int-recur-prop x f (fun/inverse f b)) g)
                        ((int-recur-prop x f (fun/inverse f b)) h)
                        (equal g h)))
        :by (p/and-elim-right (int-recur x f (fun/inverse f b))))
  (assume [g (==> int T)
           h (==> int T)
           Hg ((int-recur-bijection-prop x f b) g)
           Hh ((int-recur-bijection-prop x f b) h)]
    (have <a> ((int-recur-prop x f (fun/inverse f b)) g)
          :by (p/and-intro
               (p/and-elim-left Hg)
               ((int-recur-bijection-lemma-2 T f b g)
                (p/and-elim-right Hg))))
    (have <b> ((int-recur-prop x f (fun/inverse f b)) h)
          :by (p/and-intro
               (p/and-elim-left Hh)
               ((int-recur-bijection-lemma-2 T f b h)
                (p/and-elim-right Hh))))
    (have <c> (equal g h) :by (<single> g h <a> <b>)))
  (qed <c>))

(proof 'int-recur-bijection-thm
  (qed (p/and-intro (int-recur-bijection-ex x f b)
                    (int-recur-bijection-single x f b))))



