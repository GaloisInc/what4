(set-logic QF_LRA)
(declare-const x Real)
(assert (= (+ (* 2.0 3.0) (/ 10.0 2.0)) 11.0))
(check-sat)
