
(ns latte-integers.arith
  "The arithmetic functions over ℤ."

  (:refer-clojure :exclude [and or not int])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          try-proof ==>]]

            [latte.prop :as p :refer [and or not <=>]]
            [latte.equal :as eq :refer [equal]]
            [latte.quant :as q]
            [latte.classic :as classic]
            [latte.fun :as fun]

            [latte-sets.core :as set :refer [elem forall-in]]

            [latte-integers.core :as int :refer [zero succ pred int]]
            [latte-integers.nat :as nat :refer [positive negative]]))

(defaxiom int-recur
  "The recursion principle for integers.

According to [TT&FP,p. 318], this is derivable,
 but we introduce it as an axiom since the
derivation seems rather complex."
  [[T :type] [x T] [f-succ (==> T T)] [f-pred (==> T T)]]
  (q/unique
   (==> int T)
   (lambda [g (==> int T)]
     (and (equal T (g zero) x)
          (forall [y int]
            (and (==> (positive (succ y))
                      (equal T (g (succ y)) (f-succ (g y))))
                 (==> (negative (pred  y))
                      (equal T (g (pred y)) (f-pred (g y))))))))))

(defthm int-recur-bijection
  "The recursion principle for integers, for bijections."
  [[T :type] [x T] [f (==> T T)] [b (fun/bijective T T f)]]
  (q/unique
   (==> int T)
   (lambda [g (==> int T)]
     (and (equal T (g zero) x)
          (forall [y int]
            (equal T (g (succ y)) (f (g y))))))))

#_(deflemma int-recur-bijection-lemma-1
  [[T :type] [f (==> T T)] [b (fun/bijective T T f)] [g (==> int T)]]
  (==> (forall [y int]
         (and (==> (positive (succ y))
                   (equal T (g (succ y)) (f (g y))))
              (==> (negative (pred y))
                   (equal T (g (pred y)) ((fun/inverse T T f b) (g y))))))
       (forall [y int]
         (equal T (g (succ y)) (f (g y))))))

#_(try-proof int-recur-bijection-lemma-1
    :script
  (have inv-f _ :by (fun/inverse T T f b))
  (assume [H (and (==> (positive (succ y))
                       (equal T (g (succ y)) (f (g y))))
                  (==> (negative (pred y))
                       (equal T (g (pred y)) (inv-f (g y)))))]
    (assume [Hpos (positive (succ y))]
      (have <a> (equal T (g (succ y)) (f (g y)))
            :by ((p/and-elim-left% H) Hpos)))
    (assume [Hneg (negative (pred y))]
      (have <b1> (equal T (g (pred y)) (inv-f (g y)))
            :by ((p/and-elim-right% H) Hneg))
      (have <b2> (equal T (f (g (pred y))) (f (inv-f (g y))))
            :by ((eq/eq-cong T T f (g (pred y)) (inv-f (g y)))
                 <b1>))
      (have <b3> (equal T (f (inv-f (g y))) (g y))
            :by ((fun/inverse-prop T T f b)
                 (g y)))
      (have <b4> (equal T (g y) (f (g (pred y))))
            :by ((eq/eq-sym T (f (g (pred y))) (g y))
                 ((eq/eq-trans T (f (g (pred y))) (f (inv-f (g y))) (g y))
                  <b2> <b3>))))))

;;                -1
;;   g(y - 1) =  f  (g(y))
;;                    -1
;; ==> f(g(y-1)) = f(f  (g(y)))
;; ==> f(g(y-1)) = g(y)
;; ==> f(g(y-1+1)) = g(y+1)
;; ==> f(g(y)) = g(y+1)

(try-proof int-recur-bijection
           :script
           (have inv-f _ :by (fun/inverse T T f b))
           )
