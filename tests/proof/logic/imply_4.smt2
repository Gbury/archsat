(assert (and a b (=> a (=> b c)) (not c)))
(check-sat)
