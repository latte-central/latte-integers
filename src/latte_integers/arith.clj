
(ns latte-integers.arith
  "The arithmetic functions over ℤ."

  (:refer-clojure :exclude [and or not int])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          lambda forall proof assume have
                                          ==>]]

            [latte.prop :as p :refer [and or not <=>]]

            [latte.equal :as eq :refer [equal]]

            [latte.quant :as q]

            [latte-integers.core :as int :refer [zero succ pred int]]

            [latte-sets.core :as set :refer [elem forall-in]]

            [latte.classic :as classic]

            [latte-integers.core :as int :refer [succ pred]]

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
            (and (==> (positive y)
                      (equal T (g (succ y)) (f-succ (g y))))
                 (==> (negative y)
                      (equal T (g (pred y)) (f-pred (g y))))))))))


