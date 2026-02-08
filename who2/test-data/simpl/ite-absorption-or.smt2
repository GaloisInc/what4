(declare-const c Bool)
(declare-const y Bool)
(assert (= (or c y) (ite c c y)))
(check-sat) ; sat
(exit)
