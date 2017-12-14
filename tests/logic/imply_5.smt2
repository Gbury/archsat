(assert (not a))
(assert (not b))
(assert (=> (not a) b))
(check-sat)
