(set-logic QF_LRA)
(declare-const x Real)
(assert (= (* x 2.0) 10.0))
(check-sat)
