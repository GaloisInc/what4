; TODO: This test fails because w4smt2 doesn't support xor
; (declare-const x Bool)
; (assert (= (not x) (xor true x)))
(check-sat) ; sat
; (exit)
