(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= (bvmul x y) (bvmul y x)))
(check-sat) ; sat
(exit)
