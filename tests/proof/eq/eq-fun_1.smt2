(assert (= a b))
(assert (not (= (f a) (f b))))
(check-sat)
