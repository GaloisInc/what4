(set-logic QF_UFBV)
(declare-fun add ((_ BitVec 16) (_ BitVec 16)) (_ BitVec 16))
(assert (= (add #x0064 #x00c8) (add #x0064 #x00c8)))
(check-sat)
