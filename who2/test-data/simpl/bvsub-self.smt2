(declare-const x (_ BitVec 4))
(assert (= #b0000 (bvsub x x)))
(check-sat) ; sat
(exit)
