(set-logic BV)

(define-fun hd13 ((x (_ BitVec 64))) (_ BitVec 64)
    (bvor (bvashr x #x000000000000001F) (bvlshr (bvneg x) #x000000000000001F)))
(synth-fun f ((x (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) ((bvnot Start) (bvxor Start Start) (bvand Start Start) (bvor Start Start) (bvneg Start) (bvadd Start Start) (bvmul Start Start) (bvudiv Start Start) (bvurem Start Start) (bvlshr Start Start) (bvashr Start Start) (bvshl Start Start) (bvsdiv Start Start) (bvsrem Start Start) (bvsub Start Start) x #x000000000000001F #x0000000000000001 #x0000000000000000 #xFFFFFFFFFFFFFFFF))))

(declare-var x (_ BitVec 64))
(constraint (= (hd13 x) (f x)))

(check-synth)

