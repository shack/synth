(set-logic BV)

(synth-fun f ((x (_ BitVec 4))) (_ BitVec 4)
    ((Start (_ BitVec 4)))
    ((Start (_ BitVec 4) (
        (bvand Start Start)
        (bvor  Start Start)
        (bvxor Start Start)
        (bvsub Start Start)
        (bvshl Start Start)
        (bvlshr Start Start)
        (bvashr Start Start)
        (Variable (_ BitVec 4))
        (Constant (_ BitVec 4))
        ))))

(declare-var x (_ BitVec 4))
(constraint
    (ite
        (or (= x #x0)
        (or (= x #x1)
        (or (= x #x2)
        (or (= x #x4) (= x #x8)))))
        (= (f x) #x0)
        (not (= (f x) #x0)))
)

(check-synth)

