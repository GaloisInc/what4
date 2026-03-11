(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(assert (= y (ite false x y)))
(check-sat) ; sat
(exit)
