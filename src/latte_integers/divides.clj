(ns latte-integers.divides
  
  "The divisibility relation defined on ℤ."
  
  (:refer-clojure :exclude [and or not int = + - *])

  (:require [latte.core :as latte :refer [defaxiom defthm definition
                                          deflemma
                                          lambda forall proof assume have
                                          pose try-proof ==>]]

            [latte.prop :as p :refer [and or not <=>]]
            [latte.equal :as eq :refer [equal]]
            [latte.quant :as q :refer [exists]]
            [latte.fun :as fun]

            [latte-sets.core :as set :refer [elem forall-in]]

            [latte-integers.core :as int :refer [zero succ pred int =]]
            [latte-integers.nat :as nat :refer [nat positive negative]]
            [latte-integers.rec :as rec]
            [latte-integers.plus :as plus :refer [+]]
            [latte-integers.minus :as minus :refer [-]]
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

;; (proof divides-zero
;;     :script

;;   "TODO"
  
;;   )

(defthm divides-zero-zero
  [[n int]]
  (==> (divides zero n)
       (= n zero)))

;; (proof divides-zero-zero
;;     :script
;;   (assume [Hn (divides zero n)]
;;     (assume [p int
;;              Hp (= (* zero n) p)]
;;       (have <a1> (= zero (* zero n))
;;             :by (eq/eq-sym% (times/times-zero-swap n)))
;;       (have <a2> (= zero p)))))
