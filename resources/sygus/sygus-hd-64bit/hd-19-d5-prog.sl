(set-logic BV)

(define-fun hd19 ((x (_ BitVec 64)) (m (_ BitVec 64)) (k (_ BitVec 64))) (_ BitVec 64)
    (bvxor x (bvxor (bvshl (bvand (bvxor (bvlshr x k) x) m) k) (bvand (bvxor (bvlshr x k) x) m))))
(synth-fun f ((x (_ BitVec 64)) (m (_ BitVec 64)) (k (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) ((bvnot Start) (bvxor Start Start) (bvand Start Start) (bvor Start Start) (bvneg Start) (bvadd Start Start) (bvmul Start Start) (bvudiv Start Start) (bvurem Start Start) (bvlshr Start Start) (bvashr Start Start) (bvshl Start Start) (bvsdiv Start Start) (bvsrem Start Start) (bvsub Start Start) x m k #x000000000000001F #x0000000000000001 #x0000000000000000 #xFFFFFFFFFFFFFFFF))))

(declare-var x (_ BitVec 64))
(declare-var m (_ BitVec 64))
(declare-var k (_ BitVec 64))
(constraint (= (hd19 x m k) (f x m k)))

(check-synth)

