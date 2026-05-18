(set-logic QF_BV)
(set-info :status unsat)
;; See Note [SMT-LIB division] in What4.Interface.
(assert (= (bvsdiv #x5 #x0) #x5))
(check-sat)
