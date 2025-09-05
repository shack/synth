(set-logic BV)

(define-fun hd06 ((x (_ BitVec 64))) (_ BitVec 64)
    (bvor x (bvadd x #x0000000000000001)))
(synth-fun f ((x (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) ((bvadd Start Start) (bvor Start Start) #x0000000000000001 x))))

(declare-var x (_ BitVec 64))
(constraint (= (hd06 x) (f x)))

(check-synth)

