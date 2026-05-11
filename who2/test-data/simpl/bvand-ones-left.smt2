(declare-const x (_ BitVec 4))
(assert (= x (bvand #b1111 x)))
(check-sat) ; sat
(exit)
