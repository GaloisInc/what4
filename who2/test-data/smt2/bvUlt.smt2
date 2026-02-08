(set-logic QF_BV)
(assert (= (bvult #x0a #x14) (bvult #x0a #x14)))
(check-sat)
