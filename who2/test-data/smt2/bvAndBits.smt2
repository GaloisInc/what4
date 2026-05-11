(set-logic QF_BV)
(assert (= (bvand #xff #x0f) (bvand #xff #x0f)))
(check-sat)
