(set-logic LIA)

(define-fun max ((x Int) (y Int)) Int (ite (< x y) y x))
(define-fun min ((x Int) (y Int)) Int (ite (< x y) x y))

(synth-fun fst ((x Int) (y Int) (z Int)) Int
    ((Start Int))
    ((Start Int (
        (max Start Start)
        (min Start Start)
        (Variable Int)
        ))))
(synth-fun snd ((x Int) (y Int) (z Int)) Int
    ((Start Int))
    ((Start Int (
        (max Start Start)
        (min Start Start)
        (Variable Int)
        ))))
(synth-fun trd ((x Int) (y Int) (z Int)) Int
    ((Start Int))
    ((Start Int (
        (max Start Start)
        (min Start Start)
        (Variable Int)
        ))))

(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(assume (distinct x y z))
(assume (and (<= 0 x) (< x 3)))
(assume (and (<= 0 y) (< y 3)))
(assume (and (<= 0 z) (< z 3)))
(constraint (and (and (= (fst x y z) 0) (= (snd x y z) 1)) (= (trd x y z) 2)))

(check-synth)

