% #expect: unsat

tff(a, type, (a : $i)).

tff(goal, conjecture, ? [Y] : ! [X] : (f(Y) => f(X))).

