(set-logic BV)

(define-fun hd04 ((x (_ BitVec 8))) (_ BitVec 8)
    (bvxor x (bvsub x #x01)))
(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8)
    ((Start (_ BitVec 8)))
    ((Start (_ BitVec 8) ((bvsub Start Start) (bvxor Start Start) (bvneg Start) (bvadd Start Start) (bvor Start Start) (bvand Start Start) #x00 #x01 #xff x))))

(declare-var x (_ BitVec 8))
(constraint (= (hd04 x) (f x)))

(check-synth)

