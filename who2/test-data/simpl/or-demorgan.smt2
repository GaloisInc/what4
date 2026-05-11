(declare-const x Bool)
(declare-const y Bool)
(assert (= (or (not x) (not y)) (not (and x y))))
(check-sat) ; sat
(exit)
