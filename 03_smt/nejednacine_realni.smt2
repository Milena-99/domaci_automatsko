set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)

(assert
        (and
        (> (+ (* 3 x) (* 8 y)) 5)
        (< (- x (* 6 y)) 6)
        )
)

(check-sat)

(get-value (x y))
(exit)

