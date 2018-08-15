% #expect: unsat

tff(w, type, w : !> [ A : $tType ] : A ).

tff(ax, axiom, ? [ A : $tType , X : A ] : X != X ).

tff(goal, conjecture, $false ).

