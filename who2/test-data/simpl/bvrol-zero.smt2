; Test: rotate left by 0 is identity
(declare-const x (_ BitVec 4))
(assert (= x ((_ rotate_left 0) x)))
(check-sat) ; sat
(exit)
