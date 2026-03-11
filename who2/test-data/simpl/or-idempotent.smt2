(declare-const x Bool)
(assert (= x (or x x)))
(check-sat) ; sat
(exit)
