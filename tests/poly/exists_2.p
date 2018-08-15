% #expect: unsat

tff(w, type, w : !> [ A : $tType ] : A ).

tff(ax, axiom, ? [ A : $tType , X : A , Y : A ] : ( X = Y & X != Y ) ).

tff(goal, conjecture, $false ).
