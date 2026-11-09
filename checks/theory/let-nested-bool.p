% A Boolean $let bound to another Boolean $let, with the bound symbol occurring
% twice in the same disjunction. Inlining put the same formula into two
% generalised literals of one generalised clause and NewCNF expanded only one
% of them, so the other survived clausification as a non-literal and -newcnf on
% crashed on it. The axiom clausifies to ~q | r and ~q | p, so together with q
% and ~r the problem is unsatisfiable.
tff(p,type,
    p: $o ).

tff(q,type,
    q: $o ).

tff(r,type,
    r: $o ).

tff(let_nested_bool,axiom,
    $let(b: $o,
      b := $let(c: $o, c := ( r & p ), c ),
      ( ( q => b )
      | b ) ) ).

tff(q_holds,axiom,
    q ).

tff(r_fails,axiom,
    ~ r ).
