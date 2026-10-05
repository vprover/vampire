% Two Boolean $lets in one conjecture. NewCNF indexed each inlined definition
% without its leading negation while the generalised clause kept it, so
% clausifying one $let copied the other's literal and flipped its sign a
% second time. Its clauses became tautologies and were dropped, and -newcnf on
% answered CounterSatisfiable. Both definitions are tautologies, so the
% conjecture is a theorem.
tff(q,type,
    q: $o ).

tff(let_bool_twice,conjecture,
    ( $let(b: $o, b := ( q | ~ q ), b )
    & $let(d: $o, d := ( q | ~ q ), d ) ) ).
