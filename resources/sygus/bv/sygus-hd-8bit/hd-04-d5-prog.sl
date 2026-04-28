(set-logic BV)

(define-fun hd04 ((x (_ BitVec 8))) (_ BitVec 8)
    (bvxor x (bvsub x #x01)))
(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8)
    ((Start (_ BitVec 8)))
    ((Start (_ BitVec 8) ((bvnot Start) (bvand Start Start) (bvxor Start Start) (bvor Start Start) (bvneg Start) (bvadd Start Start) (bvmul Start Start) (bvudiv Start Start) (bvurem Start Start) (bvlshr Start Start) (bvashr Start Start) (bvshl Start Start) (bvsdiv Start Start) (bvsrem Start Start) (bvsub Start Start) #x00 #x01 #xff x))))

(declare-var x (_ BitVec 8))
(constraint (= (hd04 x) (f x)))

(check-synth)

