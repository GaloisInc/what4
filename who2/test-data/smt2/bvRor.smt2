(set-logic QF_BV)
(assert (= ((_ rotate_right 2) #xf0) ((_ rotate_right 2) #xf0)))
(check-sat)
