(set-logic BV)

(define-fun hd07 ((x (_ BitVec 8))) (_ BitVec 8)
    (bvand (bvnot x) (bvadd x #x01)))
(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8)
    ((Start (_ BitVec 8)))
    ((Start (_ BitVec 8) ((bvadd Start Start) (bvsub Start Start) (bvnot Start) (bvneg Start) (bvand Start Start) (bvor Start Start) (bvxor Start Start) #x00 #x01 #xff x))))

(declare-var x (_ BitVec 8))
(constraint (= (hd07 x) (f x)))

(check-synth)

