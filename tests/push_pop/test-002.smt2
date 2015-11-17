(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(assert (or a b c))
(check-sat) ; expect: SAT
(push 1)
(assert (not a))
(check-sat) ; expect: SAT
(push 1)
(assert (or a (not b)))
(check-sat) ; expect: SAT
(push 1)
(assert (or a (not c)))
(check-sat) ; expect: UNSAT
(pop 1)
(check-sat) ; expect: SAT
(pop 1)
(check-sat) ; expect: SAT
(pop 1)
(check-sat) ; expect SAT
