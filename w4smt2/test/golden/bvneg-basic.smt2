(declare-const x (_ BitVec 8))
(assert (= (bvneg #b00000001) #b11111111))
(check-sat)
