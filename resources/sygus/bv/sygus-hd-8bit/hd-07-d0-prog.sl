(set-logic BV)

(define-fun hd07 ((x (_ BitVec 8))) (_ BitVec 8)
    (bvand (bvnot x) (bvadd x #x01)))
(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8)
    ((Start (_ BitVec 8)))
    ((Start (_ BitVec 8) ((bvadd Start Start) (bvnot Start) (bvand Start Start) #x01 x))))

(declare-var x (_ BitVec 8))
(constraint (= (hd07 x) (f x)))

(check-synth)

