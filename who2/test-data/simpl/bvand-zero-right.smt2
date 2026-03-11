(declare-const x (_ BitVec 4))
(assert (= #b0000 (bvand x #b0000)))
(check-sat) ; sat
(exit)
