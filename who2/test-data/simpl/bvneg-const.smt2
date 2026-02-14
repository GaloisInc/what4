(declare-const x (_ BitVec 4))
(assert (= #b1111 (bvneg #b0001)))
(check-sat) ; sat
(exit)
