% #expect: unsat

fof(ax, axiom, ! [ X ] : p(X) ).

fof(ax, axiom, ! [ Y ] : ~ p(Y) ).

fof(goal, conjecture, false ).

