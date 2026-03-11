(declare-const x Bool)
(assert (= true (or x (not x))))
(check-sat) ; sat
(exit)
