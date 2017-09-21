(assert (not a))
(assert (not (or (not a) b)))
(check-sat)
