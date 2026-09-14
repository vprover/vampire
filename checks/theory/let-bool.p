% A $let binding a nullary Boolean symbol, shadowing a global of the same name.
% The definition used to be built by passing a predicate number to Term::create,
% which then read past the end of the function signature. The definition is a
% tautology, so the conjecture is a theorem.
tff(q,type,
    q: $o ).

tff(let_bool,conjecture,
    $let(q: $o,
      q := ( q | ~ q ),
      q ) ).
