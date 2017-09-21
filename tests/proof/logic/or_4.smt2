(assert a)
(assert (not b))
(assert (or (not a) b))
(check-sat)
