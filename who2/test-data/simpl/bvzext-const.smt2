(declare-const x (_ BitVec 4))
(assert (= #b00001011 ((_ zero_extend 4) #b1011)))
(check-sat) ; sat
(exit)
