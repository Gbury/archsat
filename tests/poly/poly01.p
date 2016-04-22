% #expect: unsat

tff(p, type, p : !> [A : $tType]: A > $o).

tff(ax, axiom, p($i,a)).

tff(goal, conjecture, ? [T : $tType]: ? [X : T]: p(T,X)).
