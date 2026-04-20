(declare-const x (_ BitVec 4))
(assert (= true (bvsle x x)))
(check-sat) ; sat
(exit)
