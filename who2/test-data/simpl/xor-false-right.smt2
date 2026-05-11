; TODO: This test fails because w4smt2 doesn't support xor
; (declare-const x Bool)
; (assert (= x (xor x false)))
(check-sat) ; sat
; (exit)
