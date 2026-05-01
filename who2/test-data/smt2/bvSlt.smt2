(set-logic QF_BV)
(assert (= (bvslt #xf6 #x14) (bvslt #xf6 #x14)))
(check-sat)
