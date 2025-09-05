(set-logic BV)

(define-fun hd14 ((x (_ BitVec 8)) (y (_ BitVec 8))) (_ BitVec 8)
    (bvadd (bvand x y) (bvlshr (bvxor x y) #x01)))
(synth-fun f ((x (_ BitVec 8)) (y (_ BitVec 8))) (_ BitVec 8)
    ((Start (_ BitVec 8)))
    ((Start (_ BitVec 8) ((bvnot Start) (bvxor Start Start) (bvand Start Start) (bvor Start Start) (bvneg Start) (bvadd Start Start) (bvmul Start Start) (bvudiv Start Start) (bvurem Start Start) (bvlshr Start Start) (bvashr Start Start) (bvshl Start Start) (bvsdiv Start Start) (bvsrem Start Start) (bvsub Start Start) x y #x1F #x01 #x00 #xff))))

(declare-var x (_ BitVec 8))
(declare-var y (_ BitVec 8))
(constraint (= (hd14 x y) (f x y)))

(check-synth)

