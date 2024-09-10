fof(a1,external,?[Capital,Country]:capitalCity(Capital,Country),"$XDB/scripts/externSql.py").

% fof(c,question,?[X,Y]:capitalCity(X,Y)).
% fof(conj,conjecture,?[X]:(inhabits(john,X) & capitalCity(X,czechia))).
% fof(conj,conjecture,(inhabits(john,czechia))).

fof(a2,axiom,inhabits(john,prague)).
fof(a3,axiom,(inhabits(X,Y) & capitalCity(Y,Z) => inhabits(X,Z))).
fof(a4,axiom,(inhabits(X,czechia) => attribute(X,happy))).

fof(conj,conjecture,attribute(john,happy)).

