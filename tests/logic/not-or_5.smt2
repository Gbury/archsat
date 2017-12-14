(assert (not b))
(assert (not (or a (not b) (not c))))
(check-sat)
