% #expect: unsat

fof(ax, axiom, ~ ? [ X , Y ] : ~ ( p(X) & q(Y) ) ).

fof(goal, conjecture, p(a) ).

