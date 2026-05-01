; Test: rotate 0011 right by 1 = 1001
(assert (= #b1001 ((_ rotate_right 1) #b0011)))
(check-sat) ; sat
(exit)
