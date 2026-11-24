% A sort the model has no domain for, mentioned by symbols the model has to print anyway.
%
% Only c and d occur in a clause, so FMB models t alone; s is mentioned by no clause and gets
% size 0, "this model says nothing about s". But f, g, k and p are declared, and every
% declared symbol is printed, if only with its trivial value, which means naming elements of s.
% The evaluation (and the self-check with it) treats a domain-less sort as a singleton, so
% the model has to print s as one, too; it used to print no domain for s and then
% crash looking up a name for its element: f as an argument sort, g as a result sort, k as
% a constant, p as a predicate argument. Each of the four crashed on its own.
%
% Found on Problems/ITP/ITP383_10.p with
% --decode fmb+10_1_bce=on:fmbas=function:fmbsr=1.2:fde=unused:nm=0_846

tff(s_type,type,s: $tType).
tff(t_type,type,t: $tType).
tff(f_type,type,f: s > t).
tff(g_type,type,g: t > s).
tff(k_type,type,k: s).
tff(p_type,type,p: s > $o).
tff(c_type,type,c: t).
tff(d_type,type,d: t).

tff(cd,axiom, c != d).
