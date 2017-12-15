(defproject latte-integers "0.7.1-SNAPSHOT"
  :description "A formalization of integers in LaTTe."
  :url "https://github.com/fredokun/latte-integers.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.9.0-RC1"]
                 [latte "0.100.0-SNAPSHOT"]
                 [latte-sets "0.5.0-SNAPSHOT"]]
  :codox {:output-path "docs/"
          :metadata {:doc/format :markdown}
          :namespaces [latte-integers.core latte-integers.nat
                       latte-integers.rec latte-integers.plus
                       latte-integers.minus latte-integers.ord
                       latte-integers.times latte-integers.divides]}
  :plugins [[lein-codox "0.10.3"]])

