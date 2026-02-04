(set-logic QF_UFLIA)
(declare-fun f (Int) Bool)
(assert (f 42))
(check-sat)
