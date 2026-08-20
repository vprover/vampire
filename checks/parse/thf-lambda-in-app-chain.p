% Parser regression test (binders as application arguments): a binder body is
% a single <thf_unit_formula>, so a binder is complete once its body is
% parsed, and a following '@' applies the completed binder within the
% enclosing context -- all legal THF (no leniency, no warning). The
% application-absorbing leniency used to pull the '@' into the binder body
% instead, misreading a1 as f @ (^[X]: (X @ ^[Y]: Y)) and crashing on the
% ill-sorted application.
% a1 distilled from ITP128^1.p (fact_149_let__rsp): the '@' continues the
%    enclosing application chain;
% a2 is HOL4's BETA_THM (cf. Axioms/ITP001/ITP003^7.ax): the '@' applies the
%    lambda itself, inside plain parentheses;
% a3 distilled from ITP224^4.p (fact_6643_eventually__ex): the body belongs
%    to a quantifier nested inside the lambda;
% a4 is HOL4's ABS_SIMP: a bare (unparenthesized) atomic body, the '@'
%    applies the lambda;
% a5 distilled from ITP218^2.p (fact_3380_partition__in__shuffles): the body
%    is '~ ( r @ X @ w )', a complete <thf_prefix_unary>, and the '@'
%    applies the lambda.
% Expected: a1 = (f @ (^[X: a]: X)) @ (^[Y: b]: Y);
%           a2 = ((^[X: a]: (g @ X)) @ y) = (g @ y);
%           a3 = (ev @ (^[X: a]: ?[Y: b]: (r @ X @ Y))) @ q;
%           a4 = ((^[X: b]: y) @ w) = y;
%           a5 = (fl @ (^[X: a]: ~(r @ X @ w))) @ q; no warning.
thf(ta, type, a: $tType).
thf(tb, type, b: $tType).
thf(tc, type, c: $tType).
thf(tf, type, f: (a > a) > (b > b) > $o).
thf(tg, type, g: a > a).
thf(ty, type, y: a).
thf(tw, type, w: b).
thf(tr, type, r: a > b > $o).
thf(tev, type, ev: (a > $o) > c > $o).
thf(tfl, type, fl: (a > $o) > c > $o).
thf(tq, type, q: c).
thf(a1, axiom, f @ ^ [X: a] : ( X ) @ ^ [Y: b] : ( Y ) ).
thf(a2, axiom, ( ^ [X: a] : ( g @ X ) @ y ) = ( g @ y ) ).
thf(a3, axiom, ev @ ^ [X: a] : ? [Y: b] : ( r @ X @ Y ) @ q ).
thf(a4, axiom, ( ^ [X: b] : y @ w ) = y ).
thf(a5, axiom, fl @ ^ [X: a] : ~ ( r @ X @ w ) @ q ).
