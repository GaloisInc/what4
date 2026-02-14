(declare-const x Bool)
(assert (= x (and x true)))
(check-sat) ; sat
(exit)
