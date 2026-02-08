(declare-const x (_ BitVec 4))
(assert (= x (bvand x #b1111)))
(check-sat) ; sat
(exit)
