(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(assert (= (bvadd #x14 (f #x0a)) (bvadd #x14 (f #x0a))))
(check-sat)
