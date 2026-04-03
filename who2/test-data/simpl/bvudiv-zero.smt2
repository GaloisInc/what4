; Test: 0 / x = 0 (zero dividend with concrete divisor)
(assert (= #b0000 (bvudiv #b0000 #b0101)))
(check-sat) ; sat
(exit)
