% #expect: unsat

fof(ax, axiom, ! [ X ] : ( $true & (
                ! [ Y ] : ( q(X) & p(a, Y) )
                )
              )
            ).

fof(ax, axiom, ! [ Z ] : ~ p(Z, a) ).

fof(goal, conjecture, false ).

