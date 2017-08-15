(assert (and (not (or (or a b) (or (or c d) e))) d))
(check-sat)
