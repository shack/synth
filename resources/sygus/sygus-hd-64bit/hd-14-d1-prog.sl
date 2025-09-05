(set-logic BV)

(define-fun hd14 ((x (_ BitVec 64)) (y (_ BitVec 64))) (_ BitVec 64)
    (bvadd (bvand x y) (bvlshr (bvxor x y) #x0000000000000001)))
(synth-fun f ((x (_ BitVec 64)) (y (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) ((bvlshr Start Start) (bvashr Start Start) (bvxor Start Start) (bvor Start Start) (bvadd Start Start) (bvsub Start Start) (bvand Start Start) (bvneg Start) (bvnot Start) x y #x0000000000000001 #x0000000000000000 #xFFFFFFFFFFFFFFFF))))

(declare-var x (_ BitVec 64))
(declare-var y (_ BitVec 64))
(constraint (= (hd14 x y) (f x y)))

(check-synth)

