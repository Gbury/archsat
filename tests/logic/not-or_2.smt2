(assert b)
(assert (not (or a b c)))
(check-sat)
