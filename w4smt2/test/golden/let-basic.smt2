(declare-const x (_ BitVec 8))
(assert (let ((?y #b00000001)) (= x ?y)))
(check-sat)
