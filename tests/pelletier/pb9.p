% #expect: unsat

fof(goal, conjecture, ((p | q) & (~ p | q) &
  (p | ~ q)) => ~ (~p | ~q)).
