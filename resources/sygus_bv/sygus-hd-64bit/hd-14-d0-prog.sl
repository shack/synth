(set-logic BV)

(define-fun hd14 ((x (_ BitVec 64)) (y (_ BitVec 64))) (_ BitVec 64)
    (bvadd (bvand x y) (bvlshr (bvxor x y) #x0000000000000001)))
(synth-fun f ((x (_ BitVec 64)) (y (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) ((bvlshr Start Start) (bvxor Start Start) (bvadd Start Start) (bvand Start Start) x y #x0000000000000001))))

(declare-var x (_ BitVec 64))
(declare-var y (_ BitVec 64))
(constraint (= (hd14 x y) (f x y)))

(check-synth)

