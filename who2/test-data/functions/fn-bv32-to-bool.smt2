(set-logic QF_UFBV)
(declare-fun isPositive ((_ BitVec 32)) Bool)
(assert (= (isPositive #x0000002a) (isPositive #x0000002a)))
(check-sat)
