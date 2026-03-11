(declare-const x (_ BitVec 4))
(assert (= x (bvxor x #b0000)))
(check-sat) ; sat
(exit)
