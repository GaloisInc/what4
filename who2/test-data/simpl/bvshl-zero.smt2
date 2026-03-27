(declare-const x (_ BitVec 4))
(assert (= x (bvshl x #b0000)))
(check-sat) ; sat
(exit)
