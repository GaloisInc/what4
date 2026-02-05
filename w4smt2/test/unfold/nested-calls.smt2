(define-fun double ((x Int)) Int (* x 2))
(assert (= (double (double 3)) 12))
(check-sat)
