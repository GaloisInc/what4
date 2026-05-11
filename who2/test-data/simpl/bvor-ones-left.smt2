(declare-const x (_ BitVec 4))
(assert (= #b1111 (bvor #b1111 x)))
(check-sat) ; sat
(exit)
