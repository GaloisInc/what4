(set-logic QF_BV)
(assert (= (bvneg #x2a) (bvneg #x2a)))
(check-sat)
