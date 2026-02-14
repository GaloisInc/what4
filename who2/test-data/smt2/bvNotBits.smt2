(set-logic QF_BV)
(assert (= (bvnot #xaa) (bvnot #xaa)))
(check-sat)
