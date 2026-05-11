(declare-const x Bool)
(assert (= x (and x x)))
(check-sat) ; sat
(exit)
