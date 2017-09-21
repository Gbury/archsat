% #expect: unsat

cnf(ax1, axiom, b != a).

cnf (ax2, axiom, d != c).

cnf(or, axiom, ( a = b | c = d ) ).

