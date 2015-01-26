
% typedefs
tff(p, type, p: $o).
tff(a, type, a: $i).
tff(b, type, b: $i).
tff(c, type, c: $i).
tff(d, type, d: $i).
tff(f, type, f: $i > $i).

% Problem
tff(test, conjecture,
    a = b => f(a) = f(b)
).

