(assert a)
(assert b)
(assert c)
(assert d)
(assert (not (and (and a b) (and c d))))
(check-sat)
