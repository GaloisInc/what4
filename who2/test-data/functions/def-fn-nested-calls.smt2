(set-logic QF_UFBV)
(assert (= (bvadd (bvadd #x05 #x01) #x01) (bvadd (bvadd #x05 #x01) #x01)))
(check-sat)
