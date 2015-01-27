
% typedefs
tff(a, type, a: $i).
tff(b, type, b: $i).
tff(c, type, c: $i).
tff(d, type, d: $i).

tff(f, type, f: $i > $i).
tff(p, type, f: $i > $o).

% Problem
tff(test, conjecture,
    a = b => (p(a) <=> p(b))
).

