(set-logic BV)

(define-fun hd09 ((x (_ BitVec 64))) (_ BitVec 64)
    (bvsub (bvxor x (bvashr x #x000000000000001F)) (bvashr x #x000000000000001F)))
(synth-fun f ((x (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) ((bvsub Start Start) (bvadd Start Start) (bvashr Start Start) (bvlshr Start Start) (bvxor Start Start) (bvand Start Start) (bvor Start Start) #x0000000000000001 #x0000000000000000 #x000000000000001F #xFFFFFFFFFFFFFFFF x))))

(declare-var x (_ BitVec 64))
(constraint (= (hd09 x) (f x)))

(check-synth)

