(declare-const x (_ BitVec 4))
(assert (= x (bvor x x)))
(check-sat) ; sat
(exit)
