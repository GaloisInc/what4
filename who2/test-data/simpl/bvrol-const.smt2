; Test: rotate 0011 left by 2 = 1100
(assert (= #b1100 ((_ rotate_left 2) #b0011)))
(check-sat) ; sat
(exit)
