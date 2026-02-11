; eq-refl-int.smt2, but with a comment
(declare-const x Int)
(assert (= x x))
(check-sat)
(exit)
