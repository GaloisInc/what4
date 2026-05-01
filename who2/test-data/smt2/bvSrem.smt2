(set-logic QF_BV)
(assert (= (bvsrem #x17 #x05) (bvsrem #x17 #x05)))
(check-sat)
