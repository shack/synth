(set-logic BV)

(define-fun hd09 ((x (_ BitVec 8))) (_ BitVec 8)
    (bvsub (bvxor x (bvashr x #x1F)) (bvashr x #x1F)))
(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8)
    ((Start (_ BitVec 8)))
    ((Start (_ BitVec 8) ((bvsub Start Start) (bvashr Start Start) (bvxor Start Start) #x1F x))))

(declare-var x (_ BitVec 8))
(constraint (= (hd09 x) (f x)))

(check-synth)

