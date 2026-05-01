(declare-const x Bool)
(declare-const y Bool)
(declare-const z Bool)
(assert (= (and x y z) (and (and x y) (and z x))))
(check-sat) ; sat
(exit)
