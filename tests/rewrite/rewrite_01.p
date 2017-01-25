% #expect: unsat

tff(r, axiom, ! [X : $i]: g(f(X)) = X).

tff(goal, conjecture, a = f(b) => g(a) = b).
