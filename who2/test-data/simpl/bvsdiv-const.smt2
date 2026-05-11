; Test: -4 / 2 = -2 (constant folding)
; In 4-bit: -4 = 0xC = #b1100, -2 = 0xE = #b1110
(assert (= #b1110 (bvsdiv #b1100 #b0010)))
(check-sat) ; sat
(exit)
