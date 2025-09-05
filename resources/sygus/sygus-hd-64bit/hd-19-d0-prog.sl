(set-logic BV)

(define-fun hd19 ((x (_ BitVec 64)) (m (_ BitVec 64)) (k (_ BitVec 64))) (_ BitVec 64)
    (bvxor x (bvxor (bvshl (bvand (bvxor (bvlshr x k) x) m) k) (bvand (bvxor (bvlshr x k) x) m))))
(synth-fun f ((x (_ BitVec 64)) (m (_ BitVec 64)) (k (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) ((bvand Start Start) (bvxor Start Start) (bvshl Start Start) (bvlshr Start Start) x m k))))

(declare-var x (_ BitVec 64))
(declare-var m (_ BitVec 64))
(declare-var k (_ BitVec 64))
(constraint (= (hd19 x m k) (f x m k)))

(check-synth)

