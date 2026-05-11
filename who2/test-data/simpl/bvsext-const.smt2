(declare-const x (_ BitVec 4))
(assert (= #b11111011 ((_ sign_extend 4) #b1011)))
(check-sat) ; sat
(exit)
