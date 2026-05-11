; Test: 6 / 2 = 3 (constant folding)
(assert (= #b0011 (bvudiv #b0110 #b0010)))
(check-sat) ; sat
(exit)
