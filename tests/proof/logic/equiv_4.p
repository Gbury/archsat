% #expect: unsat

fof(ax_p, axiom, p).
fof(ax_q, axiom, q).

fof(goal, conjecture, p <=> q).

