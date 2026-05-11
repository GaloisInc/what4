(declare-const x (_ BitVec 8))
(assert (= (bvmul (bvmul x x) x) (bvmul x (bvmul x x))))
(check-sat) ; sat
(exit)
