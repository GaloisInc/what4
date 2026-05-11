(declare-const x Bool)
(declare-const y Bool)
(declare-const z Bool)
(assert (= true (or (or x y z) (not x))))
(check-sat) ; sat
(exit)
