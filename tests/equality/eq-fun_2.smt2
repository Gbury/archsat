(assert (= a1 b1))
(assert (= a2 b2))
(assert (not (= (f a1 a2) (f b1 b2))))
(check-sat)
