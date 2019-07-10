(defproject latte-integers "0.10.0-SNAPSHOT"
  :description "A formalization of integers in LaTTe."
  :url "https://github.com/fredokun/latte-integers.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.10.0"]
                 [latte-sets "1.0b2-SNAPSHOT"]]
  :main latte-integers.main
  :aliases {"certify" ["run" ":certify"]
            "clear-cert" ["run" ":clear-cert"]}
  :codox {:output-path "docs/"
          :metadata {:doc/format :markdown}
          :namespaces [latte-integers.core latte-integers.nat
                       latte-integers.rec latte-integers.plus
                       latte-integers.minus latte-integers.ord
                       latte-integers.times latte-integers.divides]}
  :plugins [[lein-codox "0.10.6"]])

