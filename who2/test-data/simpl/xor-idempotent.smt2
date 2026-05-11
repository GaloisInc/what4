; TODO: This test fails because w4smt2 doesn't support xor
; (declare-const x Bool)
; (assert (= false (xor x x)))
(check-sat) ; sat
; (exit)
