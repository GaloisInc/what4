(set-logic QF_BV)
(assert (= ((_ rotate_left 2) #x0f) ((_ rotate_left 2) #x0f)))
(check-sat)
