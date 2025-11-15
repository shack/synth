(set-logic BV)

(define-fun hd20 ((x (_ BitVec 64))) (_ BitVec 64)
    (bvor (bvadd x (bvand (bvneg x) x)) (bvudiv (bvlshr (bvxor x (bvand (bvneg x) x)) #x0000000000000002) (bvand (bvneg x) x))))
(synth-fun f ((x (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) ((bvnot Start) (bvxor Start Start) (bvand Start Start) (bvor Start Start) (bvneg Start) (bvadd Start Start) (bvmul Start Start) (bvudiv Start Start) (bvurem Start Start) (bvlshr Start Start) (bvashr Start Start) (bvshl Start Start) (bvsdiv Start Start) (bvsrem Start Start) (bvsub Start Start) x #x000000000000001F #x0000000000000001 #x0000000000000000 #xFFFFFFFFFFFFFFFF))))

(declare-var x (_ BitVec 64))
(constraint (= (hd20 x) (f x)))

(check-synth)

