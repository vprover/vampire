% Unsatisfiable: a has at least 2 elements, b at most 2 and f gives |b| > |a|.
% With -fmbes contour, -fmbdsb pushes b past its detected maximum to 3. It must count as
% maxed from then on, or the search keeps growing it instead of concluding.
tff(a_t,type, a: $tType).
tff(b_t,type, b: $tType).
tff(c1_t,type, c1: a).
tff(c2_t,type, c2: a).
tff(d1_t,type, d1: b).
tff(d2_t,type, d2: b).
tff(f_t,type, f: a > b).
tff(dist,axiom, c1 != c2).
tff(domb,axiom, ![X:b]: (X = d1 | X = d2)).
tff(inj,axiom, ![X:a,Y:a]: (f(X) = f(Y) => X = Y)).
tff(nonsurj,axiom, ![X:a]: f(X) != d1).
