; TODO: This test fails because without hash consing, (ite c false true) creates
; a new NotPred node that has a different ID than (not c) parsed from SMT2
; (declare-const c Bool)
; (assert (= (not c) (ite c false true)))
(check-sat) ; sat
; (exit)
