(set-logic BV)

(define-fun hd03 ((x (_ BitVec 64))) (_ BitVec 64)
    (bvand x (bvneg x)))
(synth-fun f ((x (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) ((bvneg Start) (bvand Start Start) (bvor Start Start) (bvadd Start Start) (bvsub Start Start) #x0000000000000001 #x0000000000000000 #xFFFFFFFFFFFFFFFF x))))

(declare-var x (_ BitVec 64))
(constraint (= (hd03 x) (f x)))

(check-synth)

