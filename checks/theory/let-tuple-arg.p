%----Tuple terms outside any $let: as an argument and under equality.
tff(q_type,type,q: [$int,$int] > $o).
tff(ax,axiom, q([1,2])).
tff(ax2,axiom, ! [T: [$int,$int]] : ( T != [1,2] | T = [1,2] ) ).
tff(c,conjecture, ? [T: [$int,$int]] : ( q(T) & T = [1,2] ) ).
