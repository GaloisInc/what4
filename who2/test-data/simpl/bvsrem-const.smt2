; Test: -5 % 4 = -1 (constant folding)
; In 4-bit: -5 = 0xB = #b1011, -1 = 0xF = #b1111
(assert (= #b1111 (bvsrem #b1011 #b0100)))
(check-sat) ; sat
(exit)
