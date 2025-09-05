(set-logic BV)

(define-fun hd17 ((x (_ BitVec 64))) (_ BitVec 64)
    (bvand (bvadd (bvor x (bvsub x #x0000000000000001)) #x0000000000000001) x))
(synth-fun f ((x (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) ((bvand Start Start) (bvadd Start Start) (bvxor Start Start) (bvsub Start Start) (bvor Start Start) (bvnot Start) (bvneg Start) x #x0000000000000001 #x0000000000000000 #xFFFFFFFFFFFFFFFF))))

(declare-var x (_ BitVec 64))
(constraint (= (hd17 x) (f x)))

(check-synth)

