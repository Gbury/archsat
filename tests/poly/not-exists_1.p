% #expect: unsat

tff(t, type, p : !> [ A : $tType ] : (A > $o) ).

tff(ax, axiom, ~ ? [ A : $tType , X : A ] : ~ p(A, X) ).

tff(goal, conjecture, p($i, a) ).

