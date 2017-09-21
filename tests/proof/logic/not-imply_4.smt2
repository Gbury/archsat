(assert a)
(assert (not (=> (not a) b)))
(check-sat)
