(declare-const x (_ BitVec 4))
(assert (= #b0000 (bvxor x x)))
(check-sat) ; sat
(exit)
