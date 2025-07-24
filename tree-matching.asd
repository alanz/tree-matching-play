
(asdf:defsystem #:tree-matching
  :description "Matching tree templates using Regexp algorithms"
  :author "Alan Zimmerman <alan.zimm@gmail.com>"
  :license "MIT"
  :depends-on (
               #:trivia
               )
  :components ((:file "tree-matching")
               (:file "trie-map")
               ))
