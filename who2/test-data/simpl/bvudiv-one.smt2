; Test: x / 1 = x (identity)
(declare-const x (_ BitVec 4))
(assert (= x (bvudiv x #b0001)))
(check-sat) ; sat
(exit)
