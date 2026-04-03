(set-logic QF_BV)
(assert (= (bvsle #xf6 #x14) (bvsle #xf6 #x14)))
(check-sat)
