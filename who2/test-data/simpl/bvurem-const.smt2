; Test: 7 % 3 = 1 (constant folding)
(assert (= #b0001 (bvurem #b0111 #b0011)))
(check-sat) ; sat
(exit)
