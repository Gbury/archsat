(assert (and a b (=> (and a b) (or c d)) (not c) (not d)))
(check-sat)
