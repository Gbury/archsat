% #expect: unsat

tff(a, type, (a : $i)).

fof(goal, conjecture, ? [Y] : ! [X] : (f(Y) => f(X))).

