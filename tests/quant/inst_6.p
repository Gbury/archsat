% #expect: unsat

tff(a, type, ( a : $i ) ).

fof(ax1, axiom, ! [ X ] : p(X) ).

fof(ax2, axiom, ! [ Y ] : ( p(Y) => q(Y) ) ).

fof(ax3, axiom, ! [ Z ] : ~ q(Z) ).

fof(goal, conjecture, false ).

