% #expect: unsat

tff(a, type, ( a : $i ) ).

tff(ax, axiom, ? [ X , Y , Z ] : ( X = Y & Y = Z & X != Z ) ).

tff(goal, conjecture, $false ).

