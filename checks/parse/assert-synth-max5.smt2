(set-logic LIA)

(assert-synth (
    (x1 Int)
    (x2 Int)
    (x3 Int)
    (x4 Int)
    (x5 Int))
    ((y Int))
        (and
            (>= y x1)
            (>= y x2)
            (>= y x3)
            (>= y x4)
            (>= y x5)
            (or
                (= y x1)
                (= y x2)
                (= y x3)
                (= y x4)
                (= y x5)
            )
))
