(set-logic QF_BV)
(assert (= (bvadd #x0a #x14) (bvadd #x0a #x14)))
(check-sat)
