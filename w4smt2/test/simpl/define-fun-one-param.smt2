(define-fun neg ((x Bool)) Bool (not x))
(declare-const y Bool)
(assert (= (neg y) (not y)))
(check-sat)
