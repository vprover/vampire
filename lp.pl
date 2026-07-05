%prolog

:- consult(tptp).
:- dynamic(option/1).
:- dynamic(step/3).
:- dynamic(introduced/1).
:- dynamic(type/2).
:- dynamic(defined/2).
:- dynamic(split/3).
:- dynamic(proved/1).

/********************************************************************************
 * utility predicates
 ********************************************************************************/

% a literal is negative
negative(~_).

% does a formula contain an atom?
contains_atom(A, !_: F) => contains_atom(A, F).
contains_atom(A, ?_: F) => contains_atom(A, F).
contains_atom(A, F & G) => contains_atom(A, F) ; contains_atom(A, G).
contains_atom(A, F | G) => contains_atom(A, F) ; contains_atom(A, G).
contains_atom(A, F => G) => contains_atom(A, F) ; contains_atom(A, G).
contains_atom(A, F <=> G) => contains_atom(A, F) ; contains_atom(A, G).
contains_atom(A, ~F) => contains_atom(A, F).
contains_atom(A, L != R) => A = (L = R).
contains_atom(_, $false) => fail.
contains_atom(A, R) => R = A.
% TODO more cases

% does a clause contain a predicate p/n?
contains_predicate(P/N, Clause) :-
  contains_atom(Atom, Clause),
  Atom =.. [P|_], P \== (=),
  functor(Atom, P, N).

% does a clause contain a function f/n?
contains_function(F/N, Clause) :-
  contains_atom(Atom, Clause),
  sub_term(T, Atom),
  nonvar(T),
  T \== Atom,
  functor(T, F, N).

% extract literals of an original clause C:
literals($false, R) => R = [].
literals($false | C, R) => literals(C, R).
literals((S != T) | C, R) => R = [~(S = T)|D], literals(C, D).
literals((C | D) | E, R) => literals(C | D | E, R).
literals(L | C, R) => R = [L | D], literals(C, D).
literals(S != T, R) => R = [~(S = T)].
literals(L, R) => R = [L].

% a formula turns out to be a clause
formula_clause(!X: F | Split, Y, C) => formula_clause(!X: (F | Split), Y, C).
formula_clause(!X: F, Y, C) => Y = X, literals(F, C).
formula_clause(F, Y, C) => Y = [], literals(F, C).

clause_step(Name, Xs, C, Record) :-
  step(Name, F, Record),
  formula_clause(F, Xs, C).

% consider both orientations of a literal on backtracking
symmetric(F, F, Premise, Premise).
symmetric(L = R, R = L, Premise, neq_sym(Premise)).

/*
Is it possible to make S into T by rewriting From into To?
T is assumed to be ground (as a result of numbervars).
C is a 'context', i.e. S with holes punched in it where a rewrite happens.
'❌' marks the spot in C.
*/
% S is the same as T here
replace(_, _, T, T, T).
% rewrite
replace(From, T, S, T, ❌) :-
  % we don't need to rewrite below variables
  nonvar(S),
  unify_with_occurs_check(From, S).
% congruent case on F - should only happen if S != T
replace(From, To, S, T, C) :-
  % optimisation, not actually required
  dif(S, T),
  replace_under(From, To, S, T, C).

% replace, but only below one level of congruence
replace_under(From, To, S, T, C) :-
  nonvar(S),
  nonvar(T),
  S =.. [F|Ss],
  T =.. [F|Ts],
  maplist(replace(From, To), Ss, Ts, Cs),
  C =.. [F|Cs].

/********************************************************************************
 * printing routines
 ********************************************************************************/

lp(~A) => format("¬ ~@", [lp(A)]).
lp(L != R) => format("(~@ ≠ ~@)", [lp(L), lp(R)]).
lp(L = R) => format("(~@ = ~@)", [lp(L), lp(R)]).
lp(L | R) => format("(~@ ∨ ~@)", [lp(L), lp(R)]).
lp(L & R) => format("(~@ ∧ ~@)", [lp(L), lp(R)]).
lp(L => R) => format("(~@ ⇒ ~@)", [lp(L), lp(R)]).
lp(L <=> R) => format("(~@ ⇔ ~@)", [lp(L), lp(R)]).
lp(^Xs: ^Ys: F) => append(Xs, Ys, Zs), lp(^Zs: F).
lp(^[]: F) => lp(F).
lp(^Xs: F) => format("(λ~@, ~@)", [maplist(space_then_lp, Xs), lp(F)]).
lp('$LET'(X, T, E)) => format("(let ~@ ≔ ~@ in ~@)", [lp(X), lp(T), lp(E)]).
lp(F @ [X|Xs]) => format("(~@~@)", [lp(F), maplist(space_then_lp, [X|Xs])]).
lp(F @ X) => format("(~@ ~@)", [lp(F), lp(X)]).
lp(![]: F) => lp(F).
lp(![X|Xs]: F) => format("`∀ ~@, ~@", [lp_binder(X), lp(!Xs: F)]).
lp(?[]: F) => lp(F).
lp(?[X|Xs]: F) => format("`∃ ~@, ~@", [lp_binder(X), lp(?Xs: F)]).
lp(τ(X)) => format("τ ~@", [lp(X)]).
lp(ι) => format("ι").
lp(ο) => format("Prop").
lp(Domain > Range) => format("~@ → ~@", [lp(Domain), lp(Range)]).
lp(X * Y) => format("~@ → ~@", [lp(X), lp(Y)]).
% sort annotations should be discarded in terms
lp(X : _) => lp(X).
% variables should be bound with Prolog numbervars first
lp('$VAR'(N)) => format("x~d", [N]).
% named literals
lp('$LIT'(N)) => format("l~w", [N]).
lp('$LIT'(N)-_) => format("l~w", [N]).
% named subformulae
lp('$FORM'(N)) => format("f~w", [N]).
% references to input facts
% TODO clean this up wrt lp_app
lp('$INPUT'(Input)), option(gdv) => format("F.~w", [Input]).
lp('$INPUT'(Input)) => format("input_~w", [Input]).
lp('$INPUT'(Input, Args)), option(gdv) => format("(F.~w~@)", [Input, maplist(space_then_lp, Args)]).
lp('$INPUT'(Input, Args)) => format("(input_~w~@)", [Input, maplist(space_then_lp, Args)]).
lp('$PREMISE'(Premise, Args)) => format("(vampire_~w~@)", [Premise, maplist(space_then_lp, Args)]).
lp('$CONJECTURE'(Input)) => format("vampire_conjecture_~w", [Input]).
% inference steps that we didn't cover yet
lp('$TODO'(Step)) => format("begin { admit } end /* ~w */", [Step]).
lp('∨ₑ'(X, LProof, LsProof)) => format("∨ₑ ~@ ~@ ~@", [lp(X), lp(LProof), lp(LsProof)]).
% general terms
lp(T), nonvar(T) => T =.. [F|Args], lp_app(F, Args).

lp_app(F, []) => format("~@", lp_sym(F)).
lp_app(F, Args) => format("(~@~@)", [lp_sym(F), maplist(space_then_lp, Args)]).

lp_sym(F), option(gdv), \+ introduced(F) => format("S.~w", [F]).
lp_sym(F) => format("~w", [F]).

% clauses
lp_clause([]) => format("⊥").
lp_clause([~L|C]) => format("~@ ⇒ ~@", [lp(L), lp_clause(C)]).
lp_clause([L|C]) => format("¬ ~@ ⇒ ~@", [lp(L), lp_clause(C)]).
lp_clause([], Lits) => lp_clause(Lits).
lp_clause([X|Xs], Lits) => format("`∀ ~@, ~@", [lp_binder(X), lp_clause(Xs, Lits)]).

space_then_lp(T) :- format(" ~@", [lp(T)]).

lp_binder(X : S) => format("(~@ : ~@)", [lp(X), lp(S)]).
lp_binder(X) => format("(~@ : τ ι)", [lp(X)]).

/********************************************************************************
 * Proof reconstruction
 ********************************************************************************/

% give each literal in the body of a clause a name
enumerate_literals([], _, []).
enumerate_literals([H|T], N, ['$LIT'(N)-H|E]) :-
  M is N + 1,
  enumerate_literals(T, M, E).
enumerate_literals(Xs, R) :- enumerate_literals(Xs, 0, R).

% replace don't-care variables with infer_el
dont_care(infer_el).

% apply instantiation Ts and literal proofs Ls to P for a proof Term
apply_premise(P, Ts, Ls, '$PREMISE'(P, Args)) :- append(Ts, Ls, Args).

% use a literal in a proof, possible instantiating the premise
instantiate(N-K, L, Proof) :- symmetric(K, L, N, Proof).

% instantiation(C, Conclusion, LiteralProofs)
% can C be instantiated to match a subset of Conclusion modulo symmetry of equality?
% If so, proofs for each literal in LiteralProofs.
instantiation([], _, []).
instantiation([L|Rest], Conclusion, [LProof|RestProof]) :-
  member(K, Conclusion),
  instantiate(K, L, LProof),
  instantiation(Rest, Conclusion, RestProof).

% trivial Vampire steps where the conclusion is the premise,
% modulo symmetry, variable renaming and factoring
variant(Xs, Ls, Premise, ^Xs: ^Ls: Proof) :-
  prove_clause(Premise),
  clause_step(Premise, Ys, Ks, _),
  instantiation(Ks, Ls, Subproofs),
  apply_premise(Premise, Ys, Subproofs, Proof).

% give a proof term (simplified later) for rewriting:
% From -> To (justified by EqProof)
% in LBefore (justified by LProof)
% to obtain LAfter
rewrite(From, To, EqProof, LBefore, LAfter, LProof, subst('$CONTEXT'(Context), EqProof, LProof)) :-
  % since these are assumed to be literals, rewrite under one level of congruence
  replace_under(From, To, LBefore, LAfter, Context).

% rewrite one of Qs backwards (!) to get After
rewrite_literal_back(From, To, EqTerm, Qs, After, Proof) :-
  member(N-L, Qs),
  symmetric(L, Before, N, BeforeTerm),
  rewrite(To, From, EqTerm, Before, After, BeforeTerm, Proof).

major_resolution([], _, _, []).
major_resolution([K | Ks], Ls, Minor, [T | Ts]) :-
  member(L, Ls), instantiate(L, K, T),
  major_resolution(Ks, Ls, Minor, Ts).
major_resolution([K | Ks], Ls, Minor, [^[Pivot]: Subproof | Ts]) :-
  Pivot = '$LIT'(p),
  \+ negative(K),
  clause_step(Minor, Zs, Js, _),
  instantiation(Js, [Pivot-(~K)|Ls], Ss),
  apply_premise(Minor, Zs, Ss, Subproof),
  major_resolution(Ks, Ls, Minor, Ts).

resolution(Xs, Ls, Major, Minor, ^Xs: ^Ls: Proof) :-
  clause_step(Major, Ys, Ks, _),
  major_resolution(Ks, Ls, Minor, Subproofs),
  apply_premise(Major, Ys, Subproofs, Proof).

resolution(Xs, Ls, Premises, Proof) :-
  maplist(prove_clause, Premises),
  select(Major, Premises, [Minor]),
  resolution(Xs, Ls, Major, Minor, Proof).

mate_literal(N-(~_), Proof) => Proof = (^['$LIT'(p)]: ('$LIT'(p) @ N)).
mate_literal(N-_, Proof) => Proof = N.

disjunction_to_clause(_, [L], Proof) => mate_literal(L, Proof).
disjunction_to_clause(Fresh, [L|Ls], Proof) =>
  X = '$FORM'(Fresh),
  mate_literal(L, LProof),
  Proof = (^[X]: '∨ₑ'(X, LProof, LsProof)),
  Fresher is Fresh + 1,
  disjunction_to_clause(Fresher, Ls, LsProof).

disjunction_to_clause(Xs, Ls, Parent, ^Xs: ^Ls: (Subproof @ '$INPUT'(Parent, Xs))) :-
  disjunction_to_clause(0, Ls, Subproof).

avatar_component_clause(Xs, C, ^Xs: ^C: (SplitL @ Args)) :-
  select(SplitL-(~Split), C, Ls), split(Split, Ys, Ks),
  instantiation(Ks, Ls, Subproofs), append(Ys, Subproofs, Args).
avatar_component_clause([], C, ^C: (SplitL @ ^['$LIT'(p)]: ('$LIT'(p) @ L))) :-
  select(SplitL-Split, C, [L-(~P)]), split(Split, [], [P]).

unpack_splits(Premise, _, Bound, [], Proof) :-
  clause_step(Premise, Xs, Ls, _),
  instantiation(Ls, Bound, Subproofs),
  apply_premise(Premise, Xs, Subproofs, Proof).
unpack_splits(Premise, N, Bound, [(SplitLit-Split)|Rest], SplitLit @ ^Xs: ^Ks: Subproof) :-
  (split(Split, Xs, Ls) ; (Split = (~Split2), split(Split2, Xs, [L]), Ls = [~L])),
  length(Ls, SplitLength),
  enumerate_literals(Ls, N, Ks),
  append(Ks, Bound, Bound2),
  N2 is N + SplitLength,
  unpack_splits(Premise, N2, Bound2, Rest, Subproof).

avatar_split_clause(Splits, Premise, ^Splits: Proof) :-
  length(Splits, N),
  unpack_splits(Premise, N, Splits, Splits, Proof).


unit_propagate(_, [], _, []).
unit_propagate(Trail, [K|Ks], Propagate, [L|Rest]) :-
  member(L-K, Trail), !,
  unit_propagate(Trail, Ks, Propagate, Rest).
unit_propagate(Trail, [K|Ks], K, ['$LIT'(p)|Rest]) :-
  unit_propagate(Trail, Ks, K, Rest), !.

propagate(_, _, _, Propagate, SubProof, SubProof) :- var(Propagate).
propagate(Fresh, Trail, Available, ~Propagate, SubProof, Proof) :-
  Proof = '$LET'('$LIT'(Fresh), (^['$LIT'(p)]: SubProof), Continuation),
  Fresh2 is Fresh + 1,
  rup(Fresh2, ['$LIT'(Fresh)-Propagate|Trail], Available, Continuation), !.
propagate(Fresh, Trail, Available, Propagate, SubProof, Proof) :-
  Proof = ((^['$LIT'(p)]: SubProof) @ (^['$LIT'(Fresh)]: Continuation)),
  Fresh2 is Fresh + 1,
  rup(Fresh2, ['$LIT'(Fresh)-(~Propagate)|Trail], Available, Continuation), !.


rup(Fresh, Trail, Available, Proof) :-
  select(Premise, Available, Remaining),
  clause_step(Premise, [], Ls, _),
  unit_propagate(Trail, Ls, Propagate, SubProofs),
  apply_premise(Premise, [], SubProofs, SubProof),
  propagate(Fresh, Trail, Remaining, Propagate, SubProof, Proof).

rup(Ls, Premises, ^Ls: Proof) :-
  maplist(prove_clause, Premises),
  length(Ls, N),
  rup(N, Ls, Premises, Proof).

/********************************************************************************
 * Proof printing
 ********************************************************************************/

print_input(_, _) :- option(gdv).
print_input(Name, Parent) :-
  \+ option(gdv),
  step(Name, F, input(_)),
  numbervars(F),
  format("constant symbol input_~w : π ~@;\n", [Parent, lp(F)]).

avatar_definition(Name) :- proved(Name), !.
avatar_definition(Name) :-
  step(Name, Split <=> Component, _),
  formula_clause(Component, Xs, Ls),
  numbervars(Xs),
  format("         symbol ~w ≔ ~@;\n", [Split, lp_clause(Xs, Ls)]),
  assert(split(Split, Xs, Ls)),
  assert(proved(Name)).

% reconstruct and print a single clausal proof step
prove_clause(Name) :- proved(Name), !.
prove_clause(Name) :-
  step(Name, F, Record),
  numbervars(F),
  prove_clause(Name, F, Record),
  assert(proved(Name)), !. % cut: we only need one proof

prove_clause(Name, F, Record) =>
  formula_clause(F, Xs, C),
  enumerate_literals(C, Ls),
  prove_clause(Name, Xs, Ls, Record, Proof),
  term_variables(Proof, Remaining),
  maplist(dont_care, Remaining),
  format("opaque   symbol vampire_~w : π (~@) ≔ ~@;\n", [Name, lp_clause(Xs, C), lp(Proof)]).

prove_clause(Name, Xs, Ls, input(Parent), Proof) =>
  disjunction_to_clause(Xs, Ls, Parent, Proof),
  print_input(Name, Parent).
prove_clause(_, _, _, cnf_transformation([Parent]), Proof) =>
  Proof ='$TODO'(cnf_transformation(Parent)),
  prove_formula(Parent).
prove_clause(_, Xs, Ls, sat_conversion([Parent]), Proof) => variant(Xs, Ls, Parent, Proof).
prove_clause(_, Xs, Ls, avatar_contradiction_clause([Parent]), Proof) => variant(Xs, Ls, Parent, Proof).
prove_clause(_, Xs, Ls, factoring([Parent]), Proof) => variant(Xs, Ls, Parent, Proof).
prove_clause(_, Xs, Ls, duplicate_literal_removal([Parent]), Proof) => variant(Xs, Ls, Parent, Proof).
prove_clause(_, Xs, Ls, resolution(Premises), Proof) =>
  resolution(Xs, Ls, Premises, Proof).
prove_clause(_, Xs, Ls, forward_subsumption_resolution(Premises), Proof) =>
  resolution(Xs, Ls, Premises, Proof).
prove_clause(_, _, Ls, avatar_split_clause([Parent|Definitions]), Proof) =>
  prove_clause(Parent),
  maplist(avatar_definition, Definitions),
  avatar_split_clause(Ls, Parent, Proof).
prove_clause(_, Xs, Ls, avatar_component_clause([Definition]), Proof) =>
  avatar_definition(Definition),
  avatar_component_clause(Xs, Ls, Proof).
prove_clause(_, _, Ls, rat(Premises), Proof) => rup(Ls, Premises, Proof).
prove_clause(_, _, _, Record, Proof) =>
  Proof = '$TODO'(Record),
  Record =.. [_|[Parents]],
  maplist(prove_clause, Parents).

% reconstruct and print a single non-clausal proof step
prove_formula(Name) :- proved(Name), !.
prove_formula(Name) :-
  step(Name, F, Record),
  numbervars(F),
  prove_formula(Name, F, Record, Proof),
  format("opaque   symbol vampire_~w : π ~@ ≔ ~@;\n", [Name, lp(F), lp(Proof)]),
  assert(proved(Name)), !. % cut: we only need one proof

prove_formula(Name, _, input(Input), Proof) =>
  Proof = '$INPUT'(Input),
  print_input(Name, Input).
prove_formula(_, F, negated_conjecture([Conjecture]), Proof) =>
  step(Conjecture, _, input(Input)),
  Proof = '$CONJECTURE'(Input),
  numbervars(F),
  format("constant symbol ~@ : π ~@;\n", [lp('$CONJECTURE'(Input)), lp(F)]).

prove_formula(_, _, Record, Proof) =>
  Proof = '$TODO'(Record),
  Record =.. [_|[Parents]],
  maplist(prove_formula, Parents).

/********************************************************************************
 * Preprocessing and the main loop
 ********************************************************************************/

% process new-symbol records
assert_introduced(F) :- assert(introduced(F)).
record_introduced(new_symbols(_, Symbols)) => maplist(assert_introduced, Symbols).
record_introduced(inference(_, Records, _)) => maplist(record_introduced, Records).
record_introduced(introduced(_, Records, _)) => maplist(record_introduced, Records).
record_introduced(_) => true.

% transform various proof records into an appropriate unified record
process_inference(file(_, Name), input(Name)).
process_inference(introduced(definition, _, [Record]), Record).
process_inference(inference(Rule, _, Premises), Record) :- Record =.. [Rule|[Premises]].

% compute the default type for a predicate or function with n arguments
default_type(Range, 0, Range).
default_type(Range, 1, τ(ι) > Range).
default_type(Range, N, (τ(ι) * Domain) > Range) :-
  N > 1,
  M is N - 1,
  default_type(Range, M, Domain > Range).

% ensure every symbol is typed, assigning a default type if not
ensure_typed(_, Symbol, _) :- type(Symbol, _), !.
ensure_typed(Range, Symbol, Arity) :-
  default_type(Range, Arity, Type),
  assert(type(Symbol, Type)).

% insert proof steps into our own records as step(Name, Formula, Record) triples
load(Name, Formula, Inference) =>
  % record any introduced symbols for this inference
  record_introduced(Inference),
  % clean up a bit
  process_inference(Inference, Record),
  % insert a step(...) into the database
  assert(step(Name, Formula, Record)),
  % for any undeclared symbols in the formula, give them the default type
  forall(contains_function(F/N, Formula), ensure_typed(τ(ι), F, N)),
  forall(contains_predicate(P/N, Formula), ensure_typed(ο, P, N)).

load(end_of_file) :- !.
% type declaration stored in TPTP syntax
% implicit $i types resolved when formula is loaded
load(tff(_, type, F : T)) :- !, assert(type(F, T)), load_all.
load(tff(Name, _, Formula, Record)) :- load(Name, Formula, Record), load_all.
load(fof(Name, _, Formula, Record)) :- load(Name, Formula, Record), load_all.
load(cnf(Name, _, Formula, Record)) :- load(Name, Formula, Record), load_all.

% load everything available from stdin
load_all :-
  read(Atom),
  % load should call load_all again, except on EOF
  load(Atom).

print_lemmas :-
  format("\
require open Stdlib.Set;
require open Stdlib.Prop;
require open Stdlib.FOL;
require open Stdlib.Eq;

opaque   symbol neq_sym  [a] [x y : τ a] : π (x ≠ y) → π (y ≠ x) ≔ λ neqxy neqyx, neqxy (eq_sym neqyx);
opaque   symbol infer_el [a] : τ a ≔ el a;

").

print_prelude :- option(gdv), print_lemmas, nl.
print_prelude :-
  \+ option(gdv), print_lemmas,
  forall((type(Name, Type), \+ introduced(Name)),
    format("constant symbol ~w : ~@;\n", [Name, lp(Type)])), nl.

read_options :-
  (getenv("GDV", _), assert(option(gdv))) ; true.

main :-
  set_prolog_flag(occurs_check, true),
  read_options,
  % load the proof into `input` tuples in the Prolog database
  load_all,
  % based on this, print a prelude
  print_prelude,
  % then find falsum
  step(Name, $false, _), !, % cut: exactly one falsum will do
  prove_clause(Name).

:- initialization(main, main).
