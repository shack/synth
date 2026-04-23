(set-logic NRA)

(synth-fun f ((x Real)) Real
    ((Start Real))
    ((Start Real (
        (* Start Start)
        (Variable Real)
        (Constant Real)
        ))))

(declare-var x Real)
(constraint
    (= (f x) (* (* (* (* (* (* (* (* (* x x) x) x) x) x) x) x) x) x))
)

(check-synth)

