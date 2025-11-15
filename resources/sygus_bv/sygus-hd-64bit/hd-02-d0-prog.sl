(set-logic BV)

(define-fun hd02 ((x (_ BitVec 64))) (_ BitVec 64)
    (bvand x (bvadd x #x0000000000000001)))
(synth-fun f ((x (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) ((bvand Start Start) (bvadd Start Start) x #x0000000000000001))))

(declare-var x (_ BitVec 64))
(constraint (= (hd02 x) (f x)))

(check-synth)

