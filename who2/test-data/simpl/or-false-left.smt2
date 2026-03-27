(declare-const x Bool)
(assert (= x (or false x)))
(check-sat) ; sat
(exit)
