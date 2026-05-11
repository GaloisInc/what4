(declare-const x (_ BitVec 4))
(assert (= x (bvor #b0000 x)))
(check-sat) ; sat
(exit)
