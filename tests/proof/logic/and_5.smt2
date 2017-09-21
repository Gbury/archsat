(assert (and (and a (not b)) c (and (not d) e)))
(assert d)
(check-sat)
