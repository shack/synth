(set-logic BV)

(define-fun hd06 ((x (_ BitVec 8))) (_ BitVec 8)
    (bvor x (bvadd x #x01)))
(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8)
    ((Start (_ BitVec 8)))
    ((Start (_ BitVec 8) ((bvnot Start) (bvxor Start Start) (bvand Start Start) (bvor Start Start) (bvneg Start) (bvadd Start Start) (bvmul Start Start) (bvudiv Start Start) (bvurem Start Start) (bvlshr Start Start) (bvashr Start Start) (bvshl Start Start) (bvsdiv Start Start) (bvsrem Start Start) (bvsub Start Start) #x00 #xff #x01 x))))

(declare-var x (_ BitVec 8))
(constraint (= (hd06 x) (f x)))

(check-synth)

