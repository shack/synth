(set-logic BV)

(synth-fun f1 ((p1 (_ BitVec 64)) (P1 (_ BitVec 64))) (_ BitVec 64)
	((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) (p1 P1 (bvsub Start Start) (bvadd Start Start)))))

(synth-fun f2 ((p1 (_ BitVec 64)) (P1 (_ BitVec 64))) (_ BitVec 64)
	((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) (p1 P1 (bvadd Start Start)))))

(synth-fun f3 ((p1 (_ BitVec 64)) (P1 (_ BitVec 64))) (_ BitVec 64)
	((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) (p1 P1 (bvsub Start Start) (bvadd Start Start)))))

(synth-fun f4 ((p1 (_ BitVec 64)) (P1 (_ BitVec 64))) (_ BitVec 64)
	((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) (p1 P1 (bvsub Start Start) (bvadd Start Start)))))

(synth-fun f5 ((p1 (_ BitVec 64)) (P1 (_ BitVec 64))) (_ BitVec 64)
	((Start (_ BitVec 64)))
    ((Start (_ BitVec 64) (p1 P1 (bvsub Start Start) (bvadd Start Start)))))

(declare-var x (_ BitVec 64))
(declare-var y (_ BitVec 64))
(constraint (= (bvadd (f1 x y) (f1 x y)) (f2 x y)))
(constraint (= (bvsub (bvadd (f1 x y) (f2 x y)) y) (f3 x y)))
(constraint (= (bvadd (f2 x y) (f2 x y)) (f4 x y)))
(constraint (= (bvadd (f4 x y) (f1 x y)) (f5 x y)))

(check-synth)

