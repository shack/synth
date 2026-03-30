(set-logic BV)

(define-fun hd02 ((x (_ BitVec 64))) (_ BitVec 64)
    (bvand x (bvadd x #x0000000000000001)))
(synth-fun f ((x (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) ((bvnot Start) (bvxor Start Start) (bvand Start Start) (bvor Start Start) (bvneg Start) (bvadd Start Start) (bvmul Start Start) (bvudiv Start Start) (bvurem Start Start) (bvlshr Start Start) (bvashr Start Start) (bvshl Start Start) (bvsdiv Start Start) (bvsrem Start Start) (bvsub Start Start) x #x0000000000000000 #xFFFFFFFFFFFFFFFF #x0000000000000001))))

(declare-var x (_ BitVec 64))
(constraint (= (hd02 x) (f x)))

(check-synth)

