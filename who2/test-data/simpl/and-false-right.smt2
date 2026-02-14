(declare-const x Bool)
(assert (= false (and x false)))
(check-sat) ; sat
(exit)
