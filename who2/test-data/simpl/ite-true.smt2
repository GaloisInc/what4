(declare-const t Bool)
(declare-const f Bool)
(assert (= t (ite true t f)))
(check-sat) ; sat
(exit)
