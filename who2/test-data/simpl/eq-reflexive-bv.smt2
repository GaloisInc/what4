(declare-const x (_ BitVec 4))
(assert (= x x))
(check-sat) ; sat
(exit)
