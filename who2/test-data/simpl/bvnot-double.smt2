(declare-const x (_ BitVec 4))
(assert (= x (bvnot (bvnot x))))
(check-sat) ; sat
(exit)
