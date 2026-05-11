(set-logic QF_BV)
(assert (= (ite true #xff #x00) (ite true #xff #x00)))
(check-sat)
