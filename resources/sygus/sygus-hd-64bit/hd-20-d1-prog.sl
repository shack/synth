(set-logic BV)

(define-fun hd20 ((x (_ BitVec 64))) (_ BitVec 64)
    (bvor (bvadd x (bvand (bvneg x) x)) (bvudiv (bvlshr (bvxor x (bvand (bvneg x) x)) #x0000000000000002) (bvand (bvneg x) x))))
(synth-fun f ((x (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) ((bvand Start Start) (bvxor Start Start) (bvor Start Start) (bvadd Start Start) (bvsub Start Start) (bvlshr Start Start) (bvneg Start) (bvnot Start) (bvudiv Start Start) (bvsdiv Start Start) x #x0000000000000002 #x0000000000000000 #x0000000000000001))))

(declare-var x (_ BitVec 64))
(constraint (= (hd20 x) (f x)))

(check-synth)

