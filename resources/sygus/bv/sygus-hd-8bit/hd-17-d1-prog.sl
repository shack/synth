(set-logic BV)

(define-fun hd17 ((x (_ BitVec 8))) (_ BitVec 8)
    (bvand (bvadd (bvor x (bvsub x #x01)) #x01) x))
(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8)
    ((Start (_ BitVec 8)))
    ((Start (_ BitVec 8) ((bvand Start Start) (bvadd Start Start) (bvxor Start Start) (bvsub Start Start) (bvor Start Start) (bvnot Start) (bvneg Start) x #x01 #x00 #xff))))

(declare-var x (_ BitVec 8))
(constraint (= (hd17 x) (f x)))

(check-synth)

