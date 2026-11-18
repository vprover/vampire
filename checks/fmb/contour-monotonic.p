% Satisfiable: needs two domain elements, for a and for b.
% The only sort is monotonic, so under -fmbes contour its markers are unconstrained and do not
% bound the domain. With -sas cadical they come out false: the domain must not be cut down to 1.
cnf(a,axiom, p(a) ).
cnf(b,axiom, ~p(b) ).
