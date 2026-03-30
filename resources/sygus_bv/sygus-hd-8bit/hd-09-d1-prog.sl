(set-logic BV)

(define-fun hd09 ((x (_ BitVec 8))) (_ BitVec 8)
    (bvsub (bvxor x (bvashr x #x1F)) (bvashr x #x1F)))
(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8)
    ((Start (_ BitVec 8)))
    ((Start (_ BitVec 8) ((bvsub Start Start) (bvadd Start Start) (bvashr Start Start) (bvlshr Start Start) (bvxor Start Start) (bvand Start Start) (bvor Start Start) #x01 #x00 #x1F #xff x))))

(declare-var x (_ BitVec 8))
(constraint (= (hd09 x) (f x)))

(check-synth)

