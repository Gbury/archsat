
% typedefs
tff(a, type, a: $i).
tff(b, type, b: $i).
tff(c, type, c: $i).
tff(d, type, d: $i).

tff(f, type, f: $i > $i).
tff(p, type, p: $i > $o).

% Problem
tff(f_def, axiom,
    ! [X] : f(X) = X
).

tff(test, conjecture,
  p(f(a)) => p(a)
).

