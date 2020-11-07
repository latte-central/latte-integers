
(ns latte-integers.main
  (:gen-class)
  (:require [latte.main :refer [latte-main]]))

(defn -main [& args]
  (latte-main args "latte-integers"
              '[latte-integers.int
                latte-integers.nat
                latte-integers.rec
                latte-integers.plus
                latte-integers.minus
                latte-integers.ord
                latte-integers.times
                latte-integers.divides]))

