(declare-const x Bool)
(assert (= x (not (not x))))
(check-sat) ; sat
(exit)
