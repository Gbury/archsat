% #expect: unsat

fof(ax, axiom, ! [ X ] : ( $true & ( ! [ Y ] : p(X, Y) ) ) ).

fof(goal, conjecture, p(a, b) ).

