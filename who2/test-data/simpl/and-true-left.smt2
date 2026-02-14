(declare-const y Bool)
(assert (= y (and true y)))
(check-sat) ; sat
(exit)
