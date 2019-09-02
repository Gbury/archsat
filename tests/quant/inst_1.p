% #expect: unsat

tff(a, type, ( a : $i ) ).

fof(all, axiom, ! [ X ] : p(X) ).

fof(ex, axiom, ! [ Y ] : ~ p(Y) ).

fof(goal, conjecture, $false ).

