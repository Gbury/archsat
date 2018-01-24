% #expect: unsat

fof(ax, axiom, ! [ X ] : p(X) ).

fof(ax, axiom, ! [ Y ] : ( p(Y) => q(Y) ) ).

fof(ax, axiom, ! [ Z ] : ~ q(Z) ).

fof(goal, conjecture, false ).

