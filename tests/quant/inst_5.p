% #expect: unsat

fof(ax1, axiom, ! [ X ] : ( $true & (
                ! [ Y ] : ( q(X) & p(a, Y) )
                )
              )
            ).

fof(ax2, axiom, ! [ Z ] : ~ p(Z, a) ).

fof(goal, conjecture, false ).

