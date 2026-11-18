% Satisfiable: a singleton domain with r(a,a).
% Under Valgrind, sort inference must not read an offset for equality.
fof(domain,axiom,![X]:(X=a)).
fof(serial,axiom,![X]:(?[Y]:r(X,Y))).
