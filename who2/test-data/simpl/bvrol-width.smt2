; Test: rotating by width is identity
(declare-const x (_ BitVec 4))
(assert (= x ((_ rotate_left 4) x)))
(check-sat) ; sat
(exit)
