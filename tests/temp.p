
% typedefs
tff(a, type, a: $i).
tff(b, type, b: $i).
tff(c, type, c: $i).
tff(d, type, d: $i).

tff(f, type, f: $i > $i).
tff(p, type, p: $i > $o).

% Problem
tff(test, conjecture,
    ? [X, Y] : (X = a & Y = b)
).

