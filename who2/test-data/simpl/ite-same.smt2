(declare-const c Bool)
(declare-const t Bool)
(assert (= t (ite c t t)))
(check-sat) ; sat
(exit)
