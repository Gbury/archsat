(assert (and a b c
            (=> (and a b c) (or d e f))
            (not d) (not e) (not f)))
(check-sat)
