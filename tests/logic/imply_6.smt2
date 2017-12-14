(assert a)
(assert b)
(assert (=> a (not b)))
(check-sat)
