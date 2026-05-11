(declare-const x (_ BitVec 8))
(assert (= (bvadd x #x03) (bvadd #x02 (bvadd x #x01))))
(check-sat) ; sat
(exit)
