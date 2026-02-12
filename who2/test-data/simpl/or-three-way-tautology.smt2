(declare-const x Bool)
(declare-const y Bool)
(declare-const z Bool)
(declare-const w Bool)
(assert (= true (or (or x y) (or z (or w (not x))))))
(check-sat) ; sat
(exit)
