(in-package :maxima)

(def-simplifier appell_1 (a b c d x y)
    (let (z)
        (cond ((eql 0 y) 
               (ftake '$hypergeometric (ftake 'mlist a b) (ftake 'mlist d) x))
              (t (give-up)))))  