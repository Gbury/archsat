(assert (not a))
(assert b)
(assert (not (and (not a) b)))
(check-sat)
