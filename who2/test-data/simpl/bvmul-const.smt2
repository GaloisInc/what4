(declare-const x (_ BitVec 4))
(assert (= #b0110 (bvmul #b0010 #b0011)))
(check-sat) ; sat
(exit)
