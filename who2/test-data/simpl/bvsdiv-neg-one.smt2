; Test: x / -1 = -x (concrete example: 3 / -1 = -3)
; In 4-bit: 3 = #b0011, -1 = #b1111, -3 = #b1101
(assert (= #b1101 (bvsdiv #b0011 #b1111)))
(check-sat) ; sat
(exit)
