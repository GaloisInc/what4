(declare-const x (_ BitVec 4))
(assert (= x (bvsub x #b0000)))
(check-sat) ; sat
(exit)
