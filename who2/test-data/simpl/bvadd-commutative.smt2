(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= (bvadd x y) (bvadd y x)))
(check-sat) ; sat
(exit)
