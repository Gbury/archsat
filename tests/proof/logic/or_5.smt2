(assert (not a))
(assert b)
(assert (or a (not b)))
(check-sat)
