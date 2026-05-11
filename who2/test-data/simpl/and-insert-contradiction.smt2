(declare-const x Bool)
(declare-const y Bool)
(declare-const z Bool)
(assert (= false (and (and x y z) (not x))))
(check-sat) ; sat
(exit)
