% Parser regression test (ill-typed application): applying a term whose sort
% is not an arrow sort must raise a user error (it used to violate an
% assertion in endApp in debug builds and read garbage in release builds).
% Expected: rejected with 'sort mismatch in the application'.
thf(ta, type, a: $tType).
thf(tx, type, x: a).
thf(ty, type, y: a).
thf(a1, axiom, ( x @ y ) = x).
