(declare-const x (_ BitVec 4))
(assert (= (bvneg x) (bvsub #b0000 x)))
(check-sat) ; sat
(exit)
