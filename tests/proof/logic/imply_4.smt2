(assert a)
(assert b)
(assert (not c))
(assert (=> a (=> b c)))
(check-sat)
