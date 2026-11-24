% A blocked clause with both polarities of its predicate, p(a) | ~p(b): undoing its
% elimination needs a fixed point (Problem::addEliminatedBlockedClause), so it stays an
% explicit conditional flip and is printed as a $cond over the version below it. Every
% other conditional flip is a definition over that version (see fmb/cond-flip.p).
tff(a_type,type,a: $i).
tff(b_type,type,b: $i).
tff(p_type,type,p: $i > $o).
tff(distinct,axiom, a != b ).
tff(pb,axiom, p(b) ).
tff(blocked,axiom, p(a) | ~p(b) ).
