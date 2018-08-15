% #expect: unsat

tff(a, type, ( a : $i ) ).

tff(ax, axiom, ? [ X1 , X2 , X3 , X4 , X5 ] : (
  X1 = X2 & X2 = X3 & X3 = X4 & X4 = X5 & X1 != X5
  )
).

tff(goal, conjecture, $false ).

