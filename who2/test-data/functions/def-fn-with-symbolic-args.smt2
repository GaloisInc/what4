(set-logic QF_UFBV)
(declare-const bv16_6 (_ BitVec 16))
(assert (= (bvmul #x0002 bv16_6) (bvmul #x0002 bv16_6)))
(check-sat)
