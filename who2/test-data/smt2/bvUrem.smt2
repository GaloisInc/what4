(set-logic QF_BV)
(assert (= (bvurem #x17 #x05) (bvurem #x17 #x05)))
(check-sat)
