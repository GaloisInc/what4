(set-logic QF_BV)
(assert (= (bvlshr #xf0 #x02) (bvlshr #xf0 #x02)))
(check-sat)
