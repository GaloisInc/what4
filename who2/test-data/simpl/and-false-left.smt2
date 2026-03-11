(declare-const y Bool)
(assert (= false (and false y)))
(check-sat) ; sat
(exit)
