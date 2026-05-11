(declare-const x Bool)
(assert (= x (= x true)))
(check-sat) ; sat
(exit)
