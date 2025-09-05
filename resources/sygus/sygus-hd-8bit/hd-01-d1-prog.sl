(set-logic BV)

(define-fun hd01 ((x (_ BitVec 8))) (_ BitVec 8)
    (bvand x (bvsub x #x01)))
(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8)
    ((Start (_ BitVec 8)))
    ((Start (_ BitVec 8) ((bvand Start Start) (bvsub Start Start) (bvor Start Start) (bvadd Start Start) (bvxor Start Start) x #x00 #xff #x01))))

(declare-var x (_ BitVec 8))
(constraint (= (hd01 x) (f x)))

(check-synth)

