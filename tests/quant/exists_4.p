% #expect: unsat

tff(a, type, ( a : $i ) ).

tff(ax, axiom, ? [ X1 , X2 , X3 , X4 ] : ( X1 = X2 & X2 = X3 & X3 = X4 & X1 != X4 ) ).

tff(goal, conjecture, $false ).

