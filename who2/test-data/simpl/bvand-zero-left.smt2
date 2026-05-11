(declare-const x (_ BitVec 4))
(assert (= #b0000 (bvand #b0000 x)))
(check-sat) ; sat
(exit)
