(set-logic QF_BV)
(assert (= (bvule #x0a #x14) (bvule #x0a #x14)))
(check-sat)
