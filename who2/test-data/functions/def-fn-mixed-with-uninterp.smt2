(set-logic QF_UFBV)
(declare-fun hash ((_ BitVec 32)) (_ BitVec 32))
(assert (= (bvadd #x00000001 (hash #x0000002a)) (bvadd #x00000001 (hash #x0000002a))))
(check-sat)
