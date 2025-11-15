(set-logic BV)

(define-fun hd08 ((x (_ BitVec 64))) (_ BitVec 64)
    (bvand (bvnot x) (bvsub x #x0000000000000001)))
(synth-fun f ((x (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) ((bvsub Start Start) (bvnot Start) (bvand Start Start) #x0000000000000001 x))))

(declare-var x (_ BitVec 64))
(constraint (= (hd08 x) (f x)))

(check-synth)

