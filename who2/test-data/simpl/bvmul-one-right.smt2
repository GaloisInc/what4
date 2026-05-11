(declare-const x (_ BitVec 4))
(assert (= x (bvmul x #b0001)))
(check-sat) ; sat
(exit)
