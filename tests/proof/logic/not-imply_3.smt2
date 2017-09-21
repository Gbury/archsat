(assert (not b))
(assert (not (=> a (not b))))
(check-sat)
