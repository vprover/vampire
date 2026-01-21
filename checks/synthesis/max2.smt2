(set-logic LIA)

(assert-synth ((x1 Int) (x2 Int))
    ((y Int))
        (and
            (>= y x1)
            (>= y x2)
            (or (= y x1) (= y x2))
))
