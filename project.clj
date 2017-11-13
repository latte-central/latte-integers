(defproject latte-integers "0.6.0-SNAPSHOT"
  :description "A formalization of integers in LaTTe."
  :url "https://github.com/fredokun/latte-integers.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.9.0-RC1"]
                 [latte "0.99.9-SNAPSHOT"]
                 [latte-sets "0.4.1-SNAPSHOT"]]
  :codox {:output-path "docs/"
          :metadata {:doc/format :markdown}
          :namespaces [latte-integers.core latte-integers.nat
                       latte-integers.rec latte-integers.plus
                       latte-integers.minus latte-integers.ord
                       latte-integers.times latte-integers.divides]}
  :plugins [[lein-codox "0.10.3"]])

