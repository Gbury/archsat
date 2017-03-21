% #expect: error

tff(set, type, set: $tType > $tType).

tff(mem, type, mem: !>[ A : $tType ] : ((A * set(A)) > $o)).

tff(goal, conjecture, ! [ X : $int ] : ! [ S : set($int) ] : mem($_, X, S)).

