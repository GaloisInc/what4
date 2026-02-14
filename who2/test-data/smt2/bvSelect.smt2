(set-logic QF_BV)
(assert (= ((_ extract 5 2) #xff) ((_ extract 5 2) #xff)))
(check-sat)
