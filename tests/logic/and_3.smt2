(assert (and (and a b) c (and d e)))
(assert (not d))
(check-sat)
