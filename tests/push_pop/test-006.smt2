(assert (= a b))
(check-sat) ; expect: SAT
(push 1)
  (assert (= b c))
  (check-sat); expect: SAT
  (push 1)
    (assert (or (not (= a c)) (not (= a a))))
    (check-sat) ; expect: UNSAT
    (push 1)
      (assert (= c d))
      (check-sat) ; expect: UNSAT
      (pop 1)
    (check-sat) ; expect: UNSAT
    (pop 1)
  (check-sat) ; expect: SAT
  (pop 1)
(check-sat) ; expect: SAT
