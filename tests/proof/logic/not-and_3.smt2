(assert (and (not (and (and a b) (and c d))) a b c d))
(check-sat)
