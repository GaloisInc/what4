(declare-const x (_ BitVec 4))
(assert (= x (bvneg (bvneg x))))
(check-sat) ; sat
(exit)
