
% typedefs
tff(p, type, p: $i > $o).

% Problem
tff(test, conjecture,
  ? [X] : ! [Y] : (
    p(X) => p(Y)
  )
).

