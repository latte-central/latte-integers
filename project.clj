(defproject latte-integers "0.0.3"
  :description "A formalization of integers in LaTTe."
  :url "https://github.com/fredokun/latte-integers.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.8.0"]
                 [latte "0.3.6-SNAPSHOT"]
                 [latte-sets "0.0.5-SNAPSHOT"]]
  :codox {:metadata {:doc/format :markdown}
          :namespaces [latte-integers.core]}
  :plugins [[lein-codox "0.10.0"]])

