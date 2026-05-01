(declare-const x Bool)
(assert (= true (or true x)))
(check-sat) ; sat
(exit)
