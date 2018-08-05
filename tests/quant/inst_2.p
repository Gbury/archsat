% #expect: unsat

fof(all, axiom, ! [ X ] : p(X, a) ).

fof(ex, axiom, ! [ Y ] : ~ p(a, Y) ).

fof(goal, conjecture, false ).

