(set-logic BV)

(define-fun hd19 ((x (_ BitVec 8)) (m (_ BitVec 8)) (k (_ BitVec 8))) (_ BitVec 8)
    (bvxor x (bvxor (bvshl (bvand (bvxor (bvlshr x k) x) m) k) (bvand (bvxor (bvlshr x k) x) m))))
(synth-fun f ((x (_ BitVec 8)) (m (_ BitVec 8)) (k (_ BitVec 8))) (_ BitVec 8)
    ((Start (_ BitVec 8)))
    ((Start (_ BitVec 8) ((bvand Start Start) (bvxor Start Start) (bvshl Start Start) (bvlshr Start Start) x m k))))

(declare-var x (_ BitVec 8))
(declare-var m (_ BitVec 8))
(declare-var k (_ BitVec 8))
(constraint (= (hd19 x m k) (f x m k)))

(check-synth)

