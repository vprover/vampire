fof(a1,external,?[Capital,Country]:s__capitalCity(Capital,Country),"$XDB/scripts/externSql.py").

% fof(c,question,?[X,Y]:s__capitalCity(X,Y)).
% fof(conj,conjecture,?[X]:(s__inhabits(s__John,X) & s__capitalCity(X,s__Czechia))).
% fof(conj,conjecture,(s__inhabits(s__John,s__Czechia))).

fof(a2,axiom,s__inhabits(s__John,s__Prague)).
fof(a3,axiom,(s__inhabits(X,Y) & s__capitalCity(Y,Z) => s__inhabits(X,Z))).
fof(a4,axiom,(s__inhabits(X,s__Czechia) => s__attribute(X,s__Happy))).

fof(conj,conjecture,s__attribute(s__John,s__Happy)).

