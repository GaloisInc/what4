(declare-const x Bool)
(assert (= x (or x false)))
(check-sat) ; sat
(exit)
