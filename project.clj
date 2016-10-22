(defproject latte-integers "0.0.5-SNAPSHOT"
  :description "A formalization of integers in LaTTe."
  :url "https://github.com/fredokun/latte-integers.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.8.0"]
                 [latte "0.3.7-SNAPSHOT"]
                 [latte-sets "0.0.7-SNAPSHOT"]]
  :codox {:output-path "docs/"
          :metadata {:doc/format :markdown}
          :namespaces [latte-integers.core latte-integers.nat
                       latte-integers.arith]}
  :plugins [[lein-codox "0.10.0"]])

