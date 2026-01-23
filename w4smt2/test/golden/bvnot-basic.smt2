(declare-const x (_ BitVec 8))
(assert (= (bvnot #b11110000) #b00001111))
(check-sat)
