(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= (bvmul (bvmul x y) #x02) (bvmul #x02 (bvmul x y))))
(check-sat) ; sat
(exit)
