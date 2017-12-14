% #expect: unsat

fof(ax, axiom, ! [ X ] : ( $true & (
                ! [ Y ] : ( p(X) & q(Y) )
                )
              )
            ).

fof(goal, conjecture, q(a) ).

