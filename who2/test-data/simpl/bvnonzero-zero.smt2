(declare-const x (_ BitVec 4))
(assert (= false (distinct #b0000 #b0000)))
(check-sat) ; sat
(exit)
