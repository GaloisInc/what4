; Test: rotating by width is identity
(declare-const x (_ BitVec 4))
(assert (= x ((_ rotate_right 4) x)))
(check-sat) ; sat
(exit)
