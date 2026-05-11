(set-logic QF_UFBV)
(declare-const bv16_6 (_ BitVec 16))
(assert (= (= bv16_6 #x0000) (= bv16_6 #x0000)))
(check-sat)
