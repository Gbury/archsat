(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (or a b))
(check-sat) ; expect: SAT
(push 1)
(assert (not a))
(check-sat) ; expect : SAT
(push 1)
(assert (not b))
(check-sat) ; expect UNSAT
(pop 1)
(check-sat) ; expect SAT
bla ! ; fail !!
