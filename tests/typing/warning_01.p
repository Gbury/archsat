% #expect: warning
%
% File with an intentional typo: 'x' instead of 'X'
%

tff(goal, conjecture, ! [ X : $i ] : p(x) ).

