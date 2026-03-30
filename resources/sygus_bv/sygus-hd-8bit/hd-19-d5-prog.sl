(set-logic BV)

(define-fun hd19 ((x (_ BitVec 8)) (m (_ BitVec 8)) (k (_ BitVec 8))) (_ BitVec 8)
    (bvxor x (bvxor (bvshl (bvand (bvxor (bvlshr x k) x) m) k) (bvand (bvxor (bvlshr x k) x) m))))
(synth-fun f ((x (_ BitVec 8)) (m (_ BitVec 8)) (k (_ BitVec 8))) (_ BitVec 8)
    ((Start (_ BitVec 8)))
    ((Start (_ BitVec 8) ((bvnot Start) (bvxor Start Start) (bvand Start Start) (bvor Start Start) (bvneg Start) (bvadd Start Start) (bvmul Start Start) (bvudiv Start Start) (bvurem Start Start) (bvlshr Start Start) (bvashr Start Start) (bvshl Start Start) (bvsdiv Start Start) (bvsrem Start Start) (bvsub Start Start) x m k #x1F #x01 #x00 #xff))))

(declare-var x (_ BitVec 8))
(declare-var m (_ BitVec 8))
(declare-var k (_ BitVec 8))
(constraint (= (hd19 x m k) (f x m k)))

(check-synth)

