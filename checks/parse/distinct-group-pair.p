% Two distinct objects do form a usable group. Under the default dgel it is
% expanded and the strategy stays complete; under -dgel 1 the group survives and
% the strategy is correctly reported incomplete.

fof(a, axiom,
    p("x") ).

fof(b, axiom,
    p("y") ).

fof(c, axiom,
    q(c) ).
