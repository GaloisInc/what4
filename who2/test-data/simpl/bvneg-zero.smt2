(declare-const x (_ BitVec 4))
(assert (= #b0000 (bvneg #b0000)))
(check-sat) ; sat
(exit)
