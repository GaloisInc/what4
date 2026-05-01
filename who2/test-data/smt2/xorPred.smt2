(set-logic QF_BV)
(assert (= (not (= true false)) (not (= true false))))
(check-sat)
