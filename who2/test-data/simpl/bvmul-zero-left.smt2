(declare-const x (_ BitVec 4))
(assert (= #b0000 (bvmul #b0000 x)))
(check-sat) ; sat
(exit)
