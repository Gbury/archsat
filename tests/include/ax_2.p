
% Some type defs
tff(b, type, b : $i).
tff(q, type, q : $i > $o).

% Let's include ax_1 !
include('ax_1.p').

% A small axiom again
tff(ax_1, axiom, q(b)).

