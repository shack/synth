(set-logic BV)

(define-fun hd05 ((x (_ BitVec 64))) (_ BitVec 64)
    (bvor x (bvsub x #x0000000000000001)))
(synth-fun f ((x (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) ((bvnot Start) (bvxor Start Start) (bvand Start Start) (bvor Start Start) (bvneg Start) (bvadd Start Start) (bvmul Start Start) (bvudiv Start Start) (bvurem Start Start) (bvlshr Start Start) (bvashr Start Start) (bvshl Start Start) (bvsdiv Start Start) (bvsrem Start Start) (bvsub Start Start) #x0000000000000001 #x0000000000000000 #xFFFFFFFFFFFFFFFF x))))

(declare-var x (_ BitVec 64))
(constraint (= (hd05 x) (f x)))

(check-synth)

