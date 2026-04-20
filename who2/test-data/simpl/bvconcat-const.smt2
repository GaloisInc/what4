(declare-const x (_ BitVec 4))
(assert (= #b10110011 (concat #b1011 #b0011)))
(check-sat) ; sat
(exit)
