(set-logic LIA)

(synth-fun f ((x Int)) Int
    ((Start Int))
    ((Start Int (
        (* Start Start)
        (Variable Int)
        (Constant Int)
        ))))

(declare-var x Int)
(constraint
    (= (f x) (* (* (* (* (* (* (* (* (* x x) x) x) x) x) x) x) x) x))
)

(check-synth)

