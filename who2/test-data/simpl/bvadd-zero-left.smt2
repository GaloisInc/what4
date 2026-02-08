(declare-const x (_ BitVec 4))
(assert (= x (bvadd #b0000 x)))
(check-sat) ; sat
(exit)
