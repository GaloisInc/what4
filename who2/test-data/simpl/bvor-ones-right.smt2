(declare-const x (_ BitVec 4))
(assert (= #b1111 (bvor x #b1111)))
(check-sat) ; sat
(exit)
