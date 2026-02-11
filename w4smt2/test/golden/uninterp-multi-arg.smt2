(set-logic QF_UFLIA)
(declare-fun add (Int Int) Int)
(assert (= (add 2 3) 5))
(check-sat)
