(declare-const x (_ BitVec 4))
(assert (= x (bvlshr x #b0000)))
(check-sat) ; sat
(exit)
