(set-logic QF_UFBV)
(declare-fun hash ((_ BitVec 32)) (_ BitVec 32))
(assert (= (bvadd (hash #x0000002a) #x00000001) (bvadd (hash #x0000002a) #x00000001)))
(check-sat)
