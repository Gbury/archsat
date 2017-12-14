(assert a)
(assert b)
(assert (not (and a b)))
(check-sat)
