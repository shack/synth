(set-logic BV)

(define-fun hd01 ((x (_ BitVec 64))) (_ BitVec 64)
    (bvand x (bvsub x #x0000000000000001)))
(synth-fun f ((x (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) ((bvand Start Start) (bvsub Start Start) (bvor Start Start) (bvadd Start Start) (bvxor Start Start) x #x0000000000000000 #xFFFFFFFFFFFFFFFF #x0000000000000001))))

(declare-var x (_ BitVec 64))
(constraint (= (hd01 x) (f x)))

(check-synth)

