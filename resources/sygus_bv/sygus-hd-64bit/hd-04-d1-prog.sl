(set-logic BV)

(define-fun hd04 ((x (_ BitVec 64))) (_ BitVec 64)
    (bvxor x (bvsub x #x0000000000000001)))
(synth-fun f ((x (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) ((bvsub Start Start) (bvxor Start Start) (bvneg Start) (bvadd Start Start) (bvor Start Start) (bvand Start Start) #x0000000000000000 #x0000000000000001 #xFFFFFFFFFFFFFFFF x))))

(declare-var x (_ BitVec 64))
(constraint (= (hd04 x) (f x)))

(check-synth)

