(set-logic BV)

(define-fun hd05 ((x (_ BitVec 64))) (_ BitVec 64)
    (bvor x (bvsub x #x0000000000000001)))
(synth-fun f ((x (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) ((bvsub Start Start) (bvneg Start) (bvadd Start Start) (bvand Start Start) (bvxor Start Start) (bvor Start Start) #x0000000000000001 #x0000000000000000 #xFFFFFFFFFFFFFFFF x))))

(declare-var x (_ BitVec 64))
(constraint (= (hd05 x) (f x)))

(check-synth)

