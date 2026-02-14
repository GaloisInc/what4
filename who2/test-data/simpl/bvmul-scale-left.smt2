(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= (bvmul #x03 (bvmul x y)) (bvmul (bvmul x y) #x03)))
(check-sat) ; sat
(exit)
