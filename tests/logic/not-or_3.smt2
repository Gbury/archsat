(assert d)
(assert (not (or (or a b) (or (or c d) e))))
(check-sat)
