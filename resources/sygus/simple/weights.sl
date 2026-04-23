(set-logic BV)
(set-feature :weights true)
(declare-weight w0 0)
(declare-weight w1 1)

(synth-fun f ((x (_ BitVec 4))) (_ BitVec 4)
    ((Start (_ BitVec 4)))
    ((Start (_ BitVec 4) (
        (!(bvand Start Start) :w1 1)
        (bvor  Start Start)
        (bvxor Start Start)
        (!(bvadd Start Start) :w0 3)
        (!(bvsub Start Start) :w1 2)
        (!(bvshl Start Start) :weight 2)
        (!(bvlshr Start Start) :weight 2)
        (!(bvashr Start Start) :weight 2)
        (Variable (_ BitVec 4))
        (Constant (_ BitVec 4))
        ))))

(declare-var x (_ BitVec 4))
(constraint
    (and (= (_ w1 f) 4)
    (ite
        (or (= x #x0)
        (or (= x #x1)
        (or (= x #x2)
        (or (= x #x4) (= x #x8)))))
        (= (f x) #x0)
        (not (= (f x) #x0)))
    )
)

(check-synth)

