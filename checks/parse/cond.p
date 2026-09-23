% $cond(c1,v1,...,cn,vn,e) is a flat chained if/elif/.../else, and the first
% matching case wins. Here p(d) and q(d) both hold, so the value must be a and
% not b -- and since a != b is asserted, the conjecture f(d) = a is refutable
% under any other reading of the case order. That is what makes this a test of
% the semantics and not just of the grammar.

tff(alpha_type,type,alpha: $tType).
tff(a_type,type,a: alpha).
tff(b_type,type,b: alpha).
tff(c_type,type,c: alpha).
tff(d_type,type,d: alpha).
tff(f_type,type,f: alpha > alpha).
tff(g_type,type,g: ( alpha * alpha ) > alpha).
tff(p_type,type,p: alpha > $o).
tff(q_type,type,q: alpha > $o).

tff(distinct,axiom,
    a != b & a != c ).

tff(both_hold,axiom,
    p(d) & q(d) ).

% $cond in term position
tff(f_def,axiom,
    ! [X: alpha] : f(X) = $cond(p(X), a, q(X), b, c) ).

% ... and in formula position, where the branches are $o-sorted
tff(h_def,axiom,
    $cond(p(d), q(d), $false) ).

% The shape FMB model printing will emit for a conditional-flip layer: conditions
% that are conjunctions of argument equalities, sitting inside an equality argument.
% Written without parentheses, which only became possible once the parser stopped
% ending a term at a connective that follows an equality, and stopped carrying the
% equality-argument guard into a nested argument list (see parse/term-eq-connective.p).
tff(g_def,axiom,
    ! [X: alpha,Y: alpha] :
      g(X,Y) = $cond(X = a & Y = b, c, X = a, b, a) ).

% a condition of the form "A & B = C" keeps its A: it used to be read as just "B = C"
tff(k_def,axiom,
    $cond(p(d) & q(d) = $true, p(d), $true) ).

tff(goal,conjecture,
    f(d) = a & g(a,b) = c & g(a,a) = b ).
