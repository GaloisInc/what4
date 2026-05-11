(declare-const x (_ BitVec 4))
(assert (= x (bvor x #b0000)))
(check-sat) ; sat
(exit)
