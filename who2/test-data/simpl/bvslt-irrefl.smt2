(declare-const x (_ BitVec 4))
(assert (= false (bvslt x x)))
(check-sat) ; sat
(exit)
