(declare-const x (_ BitVec 4))
(assert (= x (bvxor #b0000 x)))
(check-sat) ; sat
(exit)
