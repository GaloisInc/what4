; Test: x / 1 = x (identity)
(declare-const x (_ BitVec 4))
(assert (= x (bvsdiv x #b0001)))
(check-sat) ; sat
(exit)
