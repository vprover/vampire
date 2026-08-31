%----A unary function over a tuple sort used to be mistaken for a tuple
%----projection while printing type declarations, reading past the end of
%----the tuple term algebra's destructor array (Shell/TermAlgebra.hpp:47).
tff(h_type,type,h: [$int,$int,$int] > $int).
tff(c,conjecture, h([1,2,3]) = h([1,2,3])).
