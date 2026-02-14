(declare-const c Bool)
(assert (= c (ite c true false)))
(check-sat) ; sat
(exit)
