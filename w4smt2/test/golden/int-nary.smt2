(set-logic QF_LIA)
; Test n-ary addition with constants
(assert (= (+ 1 2 3 4) 10))
; Test n-ary multiplication with constants
(assert (= (* 2 3 5) 30))
; Test with more arguments
(assert (= (+ 1 1 1 1 1 1 1 1 1 1) 10))
(check-sat)
