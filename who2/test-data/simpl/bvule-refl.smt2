(declare-const x (_ BitVec 4))
(assert (= true (bvule x x)))
(check-sat) ; sat
(exit)
