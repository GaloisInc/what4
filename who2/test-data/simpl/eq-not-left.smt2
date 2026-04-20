(declare-const x Bool)
; (not x) == true should simplify to (not x)
(assert (= (not x) (= (not x) true)))
(check-sat) ; sat
(exit)
