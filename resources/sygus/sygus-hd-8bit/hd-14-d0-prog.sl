(set-logic BV)

(define-fun hd14 ((x (_ BitVec 8)) (y (_ BitVec 8))) (_ BitVec 8)
    (bvadd (bvand x y) (bvlshr (bvxor x y) #x01)))
(synth-fun f ((x (_ BitVec 8)) (y (_ BitVec 8))) (_ BitVec 8)
    ((Start (_ BitVec 8)))
    ((Start (_ BitVec 8) ((bvlshr Start Start) (bvxor Start Start) (bvadd Start Start) (bvand Start Start) x y #x01))))

(declare-var x (_ BitVec 8))
(declare-var y (_ BitVec 8))
(constraint (= (hd14 x y) (f x y)))

(check-synth)

