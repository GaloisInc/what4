(declare-const x (_ BitVec 4))
(assert (= x (bvand x x)))
(check-sat) ; sat
(exit)
