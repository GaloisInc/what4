(set-logic QF_BV)
(assert (= ((_ sign_extend 8) #xff) ((_ sign_extend 8) #xff)))
(check-sat)
