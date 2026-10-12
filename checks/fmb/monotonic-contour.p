% Regression for the CONTOUR enumeration strategy (-fmbes contour), which reads the
% size of the found model back off the sort marker variables. For a *monotonic* sort
% (here $i: the problem has no equality at all) the markers say nothing about the
% model -- instances of such a sort are not marked and only the weakest totality
% clause is generated -- so a solver is free to return them all false, which used to
% shrink the domain to a single element.
%
% Two elements are needed here (size 1 is refuted before size 2 is tried), so a
% one-element model is wrong by construction; with -sas cadical it used to be printed
% nevertheless (with an out-of-domain value for b, at that).
fof(a1, axiom, p(a)).
fof(a2, axiom, ~p(b)).
