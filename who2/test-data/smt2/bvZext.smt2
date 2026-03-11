(set-logic QF_BV)
(assert (= ((_ zero_extend 8) #xff) ((_ zero_extend 8) #xff)))
(check-sat)
