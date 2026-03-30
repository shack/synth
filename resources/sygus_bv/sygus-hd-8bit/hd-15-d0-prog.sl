(set-logic BV)

(define-fun hd15 ((x (_ BitVec 8)) (y (_ BitVec 8))) (_ BitVec 8)
    (bvsub (bvor x y) (bvlshr (bvxor x y) #x01)))
(synth-fun f ((x (_ BitVec 8)) (y (_ BitVec 8))) (_ BitVec 8)
    ((Start (_ BitVec 8)))
    ((Start (_ BitVec 8) ((bvlshr Start Start) (bvxor Start Start) (bvsub Start Start) (bvor Start Start) x y #x01))))

(declare-var x (_ BitVec 8))
(declare-var y (_ BitVec 8))
(constraint (= (hd15 x y) (f x y)))

(check-synth)

