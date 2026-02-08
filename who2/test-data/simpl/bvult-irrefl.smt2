(declare-const x (_ BitVec 4))
(assert (= false (bvult x x)))
(check-sat) ; sat
(exit)
