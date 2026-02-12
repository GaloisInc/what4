(declare-const x Bool)
(declare-const y Bool)
(declare-const z Bool)
(assert (= (or x y z) (or (or x y) (or z x))))
(check-sat) ; sat
(exit)
