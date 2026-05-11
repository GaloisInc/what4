(declare-const x Bool)
(assert (= false (and x (not x))))
(check-sat) ; sat
(exit)
