(declare-const x Bool)
(assert (= (not x) (= x false)))
(check-sat) ; sat
(exit)
