(set-logic BV)

(define-fun hd05 ((x (_ BitVec 8))) (_ BitVec 8)
    (bvor x (bvsub x #x01)))
(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8)
    ((Start (_ BitVec 8)))
    ((Start (_ BitVec 8) ((bvsub Start Start) (bvor Start Start) #x01 x))))

(declare-var x (_ BitVec 8))
(constraint (= (hd05 x) (f x)))

(check-synth)

