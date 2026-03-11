(set-logic QF_BV)
(assert (= (bvxor #xff #xaa) (bvxor #xff #xaa)))
(check-sat)
