(declare-const x Bool)
(declare-const y Bool)
(assert (= (and (not x) (not y)) (not (or x y))))
(check-sat) ; sat
(exit)
