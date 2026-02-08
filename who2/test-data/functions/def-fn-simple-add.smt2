(set-logic QF_UFBV)
(assert (= (bvadd #x0a #x14) (bvadd #x0a #x14)))
(check-sat)
