%----An ordinary $let-bound symbol may have a tuple sort; it must not be
%----mistaken for a tuple binding [c1,...,cn] := t (which has a list of
%----bound constants, whereas this one has none).
tff(g_type,type,g: [$int,$int]).
tff(p_type,type,p: [$int,$int] > $o).
tff(ax,axiom, p(g)).
tff(c,conjecture, $let(x: [$int,$int], x := g, p(x))).
