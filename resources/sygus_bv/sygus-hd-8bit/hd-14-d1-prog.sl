(set-logic BV)

(define-fun hd14 ((x (_ BitVec 8)) (y (_ BitVec 8))) (_ BitVec 8)
    (bvadd (bvand x y) (bvlshr (bvxor x y) #x01)))
(synth-fun f ((x (_ BitVec 8)) (y (_ BitVec 8))) (_ BitVec 8)
    ((Start (_ BitVec 8)))
    ((Start (_ BitVec 8) ((bvlshr Start Start) (bvashr Start Start) (bvxor Start Start) (bvor Start Start) (bvadd Start Start) (bvsub Start Start) (bvand Start Start) (bvneg Start) (bvnot Start) x y #x01 #x00 #xff))))

(declare-var x (_ BitVec 8))
(declare-var y (_ BitVec 8))
(constraint (= (hd14 x y) (f x y)))

(check-synth)

