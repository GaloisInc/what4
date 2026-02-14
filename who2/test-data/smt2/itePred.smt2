(set-logic QF_BV)
(assert (= (ite true true false) (ite true true false)))
(check-sat)
