(set-logic QF_BV)
(set-info :status sat)
;; See Note [SMT-LIB division] in What4.Interface.
(assert (= (bvsrem #x5 #x0) #x5))
(check-sat)
