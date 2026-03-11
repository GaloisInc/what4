(declare-const x (_ BitVec 4))
(assert (= x (bvadd x #b0000)))
(check-sat) ; sat
(exit)
