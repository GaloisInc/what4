(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(assert (= x (ite true x y)))
(check-sat) ; sat
(exit)
