(set-logic QF_BV)
(assert (= (concat #xa #x5) (concat #xa #x5)))
(check-sat)
