(declare-const x (_ BitVec 4))
(assert (= #b0000 (bvmul x #b0000)))
(check-sat) ; sat
(exit)
