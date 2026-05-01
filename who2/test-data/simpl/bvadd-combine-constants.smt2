(declare-const x (_ BitVec 8))
(assert (= (bvadd x #x03) (bvadd (bvadd x #x01) #x02)))
(check-sat) ; sat
(exit)
