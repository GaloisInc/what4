(declare-const c Bool)
(declare-const y Bool)
(assert (= (or c y) (ite c true y)))
(check-sat) ; sat
(exit)
