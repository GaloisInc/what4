(declare-const x (_ BitVec 4))
(assert (= false (bvult x #b0000)))
(check-sat) ; sat
(exit)
