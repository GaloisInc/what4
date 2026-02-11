(declare-const s (_ BitVec 8))
(declare-const t (_ BitVec 8))
(assert (= (bvand s (bvnot t)) #b00000000))
(check-sat)
