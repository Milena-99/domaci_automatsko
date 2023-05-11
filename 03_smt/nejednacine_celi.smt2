(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)

(assert
	(and
	(> (+ (* 3 x) (* 8 y)) 5)
	(< (- x (* 6 y)) 6)
	)
)

(check-sat)

(get-value (x y))
(exit)
