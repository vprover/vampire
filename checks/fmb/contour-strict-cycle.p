% Has only infinite models: f and g are injective but not surjective, so a > b > a.
% -fmbdsb finds that as a cycle of strict constraints, on which -fmbes contour should give up
% instead of growing the domains (or propagating the constraints) until it runs out of time.
tff(a_t,type, a: $tType).
tff(b_t,type, b: $tType).
tff(ca_t,type, ca: a).
tff(cb_t,type, cb: b).
tff(f_t,type, f: a > b).
tff(g_t,type, g: b > a).
tff(finj,axiom, ![X:a,Y:a]: (f(X) = f(Y) => X = Y)).
tff(fnon,axiom, ![X:a]: f(X) != cb).
tff(ginj,axiom, ![X:b,Y:b]: (g(X) = g(Y) => X = Y)).
tff(gnon,axiom, ![X:b]: g(X) != ca).
