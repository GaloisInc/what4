(declare-const x Bool)
(declare-const y Bool)
(declare-const z Bool)
(declare-const w Bool)
(assert (= false (and (and x y) (and z (and w (not x))))))
(check-sat) ; sat
(exit)
