
% Some type defs
tff(c, type, c : $i).
tff(r, type, r : $i > $o).

% Let's include ax_1 !
include('ax_2.p').

% A small axiom again
tff(ax_1, axiom, r(c)).

