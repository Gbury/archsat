(assert a)
(assert (not b))
(assert (not (and a (not b))))
(check-sat)
