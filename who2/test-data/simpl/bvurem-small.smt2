; Test: x % y = x when x < y (concrete example: 2 % 5 = 2)
(assert (= #b0010 (bvurem #b0010 #b0101)))
(check-sat) ; sat
(exit)
