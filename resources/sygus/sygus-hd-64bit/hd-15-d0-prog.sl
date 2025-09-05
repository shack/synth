(set-logic BV)

(define-fun hd15 ((x (_ BitVec 64)) (y (_ BitVec 64))) (_ BitVec 64)
    (bvsub (bvor x y) (bvlshr (bvxor x y) #x0000000000000001)))
(synth-fun f ((x (_ BitVec 64)) (y (_ BitVec 64))) (_ BitVec 64)
    ((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) ((bvlshr Start Start) (bvxor Start Start) (bvsub Start Start) (bvor Start Start) x y #x0000000000000001))))

(declare-var x (_ BitVec 64))
(declare-var y (_ BitVec 64))
(constraint (= (hd15 x y) (f x y)))

(check-synth)

