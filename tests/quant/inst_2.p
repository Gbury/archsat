% #expect: unsat

fof(ax, axiom, ! [ X ] : p(X, a) ).

fof(ax, axiom, ! [ Y ] : ~ p(a, Y) ).

fof(goal, conjecture, false ).

