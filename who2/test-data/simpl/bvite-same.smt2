(declare-const x (_ BitVec 4))
(declare-const c Bool)
(assert (= x (ite c x x)))
(check-sat) ; sat
(exit)
