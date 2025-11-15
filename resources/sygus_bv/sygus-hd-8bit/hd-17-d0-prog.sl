(set-logic BV)

(define-fun hd17 ((x (_ BitVec 8))) (_ BitVec 8)
    (bvand (bvadd (bvor x (bvsub x #x01)) #x01) x))
(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8)
    ((Start (_ BitVec 8)))
    ((Start (_ BitVec 8) ((bvand Start Start) (bvadd Start Start) (bvsub Start Start) (bvor Start Start) x #x01))))

(declare-var x (_ BitVec 8))
(constraint (= (hd17 x) (f x)))

(check-synth)

