(declare-const x Bool)
(assert (= true (or x true)))
(check-sat) ; sat
(exit)
