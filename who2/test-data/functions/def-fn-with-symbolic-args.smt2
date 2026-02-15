(set-logic QF_UFBV)
(declare-const bv16_6 (_ BitVec 16))
(assert (= (bvmul bv16_6 #x0002) (bvmul bv16_6 #x0002)))
(check-sat)
