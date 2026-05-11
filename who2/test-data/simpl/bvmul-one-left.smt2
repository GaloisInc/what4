(declare-const x (_ BitVec 4))
(assert (= x (bvmul #b0001 x)))
(check-sat) ; sat
(exit)
