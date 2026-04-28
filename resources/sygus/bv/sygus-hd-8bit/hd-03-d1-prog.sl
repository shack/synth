(set-logic BV)

(define-fun hd03 ((x (_ BitVec 8))) (_ BitVec 8)
    (bvand x (bvneg x)))
(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8)
    ((Start (_ BitVec 8)))
    ((Start (_ BitVec 8) ((bvneg Start) (bvand Start Start) (bvor Start Start) (bvadd Start Start) (bvsub Start Start) #x01 #x00 #xff x))))

(declare-var x (_ BitVec 8))
(constraint (= (hd03 x) (f x)))

(check-synth)

