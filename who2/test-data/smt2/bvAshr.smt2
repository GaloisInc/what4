(set-logic QF_BV)
(assert (= (bvashr #xf0 #x02) (bvashr #xf0 #x02)))
(check-sat)
