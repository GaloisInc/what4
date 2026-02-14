(declare-const x (_ BitVec 4))
(assert (= #b11 ((_ extract 2 1) #b0110)))
(check-sat) ; sat
(exit)
