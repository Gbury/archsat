% #expect: unsat

tff(t, type, p : !> [ A : $tType , B : $tType ] : ((A * B) > $o) ).

tff(ax, axiom, ! [ A : $tType , B : $tType , X : A , Y : B ] : p(A, B, X, Y) ).

tff(goal, conjecture, p($i, $i, a, b) ).

