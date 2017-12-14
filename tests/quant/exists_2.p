% #expect: unsat

tff(a, type, ( a : $i ) ).

tff(ax, axiom, ? [ X , Y ] : ( X = Y & Y != X )).

tff(goal, conjecture, $false ).

