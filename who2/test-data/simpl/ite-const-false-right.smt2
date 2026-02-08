(declare-const c Bool)
(declare-const x Bool)
(assert (= (and c x) (ite c x false)))
(check-sat) ; sat
(exit)
