; Test: x % 1 = 0 (always zero)
(declare-const x (_ BitVec 4))
(assert (= #b0000 (bvurem x #b0001)))
(check-sat) ; sat
(exit)
