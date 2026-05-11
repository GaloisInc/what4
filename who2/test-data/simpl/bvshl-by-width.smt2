(declare-const x (_ BitVec 4))
(assert (= #b0000 (bvshl x #b0100)))
(check-sat) ; sat
(exit)
