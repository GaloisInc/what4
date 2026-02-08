(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(assert (= (f #x2a) (f #x2a)))
(check-sat)
