(set-logic BV)

(define-fun hd07 ((x (_ BitVec 64))) (_ BitVec 64)
    (bvand (bvnot x) (bvadd x #x0000000000000001)))
(synth-fun f ((x (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) ((bvadd Start Start) (bvsub Start Start) (bvnot Start) (bvneg Start) (bvand Start Start) (bvor Start Start) (bvxor Start Start) #x0000000000000000 #x0000000000000001 #xFFFFFFFFFFFFFFFF x))))

(declare-var x (_ BitVec 64))
(constraint (= (hd07 x) (f x)))

(check-synth)

