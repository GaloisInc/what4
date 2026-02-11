(set-logic QF_LRA)
(declare-const x Real)
(assert (= x (/ 3 4)))
(check-sat)
