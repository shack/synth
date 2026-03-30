(set-logic BV)

(define-fun hd20 ((x (_ BitVec 8))) (_ BitVec 8)
    (bvor (bvadd x (bvand (bvneg x) x)) (bvudiv (bvlshr (bvxor x (bvand (bvneg x) x)) #x02) (bvand (bvneg x) x))))
(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8)
    ((Start (_ BitVec 8)))
    ((Start (_ BitVec 8) ((bvand Start Start) (bvxor Start Start) (bvor Start Start) (bvadd Start Start) (bvlshr Start Start) (bvneg Start) (bvudiv Start Start) x #x02))))

(declare-var x (_ BitVec 8))
(constraint (= (hd20 x) (f x)))

(check-synth)

