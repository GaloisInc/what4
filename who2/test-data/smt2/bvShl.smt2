(set-logic QF_BV)
(assert (= (bvshl #x0f #x02) (bvshl #x0f #x02)))
(check-sat)
