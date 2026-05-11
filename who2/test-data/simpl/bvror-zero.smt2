; Test: rotate right by 0 is identity
(declare-const x (_ BitVec 4))
(assert (= x ((_ rotate_right 0) x)))
(check-sat) ; sat
(exit)
