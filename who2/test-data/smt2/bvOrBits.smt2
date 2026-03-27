(set-logic QF_BV)
(assert (= (bvor #xf0 #x0f) (bvor #xf0 #x0f)))
(check-sat)
