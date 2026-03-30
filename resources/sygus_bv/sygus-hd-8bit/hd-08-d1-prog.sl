(set-logic BV)

(define-fun hd08 ((x (_ BitVec 8))) (_ BitVec 8)
    (bvand (bvnot x) (bvsub x #x01)))
(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8)
    ((Start (_ BitVec 8)))
    ((Start (_ BitVec 8) ((bvsub Start Start) (bvadd Start Start) (bvnot Start) (bvneg Start) (bvand Start Start) (bvor Start Start) (bvxor Start Start) #x00 #x01 #xff x))))

(declare-var x (_ BitVec 8))
(constraint (= (hd08 x) (f x)))

(check-synth)

