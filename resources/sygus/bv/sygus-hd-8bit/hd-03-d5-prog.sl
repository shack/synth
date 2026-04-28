(set-logic BV)

(define-fun hd03 ((x (_ BitVec 8))) (_ BitVec 8)
    (bvand x (bvneg x)))
(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8)
    ((Start (_ BitVec 8)))
    ((Start (_ BitVec 8) ((bvnot Start) (bvand Start Start) (bvxor Start Start) (bvor Start Start) (bvneg Start) (bvadd Start Start) (bvmul Start Start) (bvudiv Start Start) (bvurem Start Start) (bvlshr Start Start) (bvashr Start Start) (bvshl Start Start) (bvsdiv Start Start) (bvsrem Start Start) (bvsub Start Start) #x01 #x00 #xff x))))

(declare-var x (_ BitVec 8))
(constraint (= (hd03 x) (f x)))

(check-synth)

