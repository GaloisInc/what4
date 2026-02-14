(declare-const t Bool)
(declare-const f Bool)
(assert (= f (ite false t f)))
(check-sat) ; sat
(exit)
