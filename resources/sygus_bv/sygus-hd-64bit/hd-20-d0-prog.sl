(set-logic BV)

(define-fun hd20 ((x (_ BitVec 64))) (_ BitVec 64)
    (bvor (bvadd x (bvand (bvneg x) x)) (bvudiv (bvlshr (bvxor x (bvand (bvneg x) x)) #x0000000000000002) (bvand (bvneg x) x))))
(synth-fun f ((x (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) ((bvand Start Start) (bvxor Start Start) (bvor Start Start) (bvadd Start Start) (bvlshr Start Start) (bvneg Start) (bvudiv Start Start) x #x0000000000000002))))

(declare-var x (_ BitVec 64))
(constraint (= (hd20 x) (f x)))

(check-synth)

