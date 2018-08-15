% #expect: unsat

tff(a, type, ( a : $i ) ).

tff(ax, axiom, ? [ X1 , X2 , X3 , X4 , X5 , X6 ] : (
  X1 = X2 & X2 = X3 & X3 = X4 & X4 = X5 & X5 = X6 & X1 != X6
  )
).

tff(goal, conjecture, $false ).

