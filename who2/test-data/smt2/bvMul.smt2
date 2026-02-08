(set-logic QF_BV)
(assert (= (bvmul #x05 #x07) (bvmul #x05 #x07)))
(check-sat)
