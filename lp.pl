%prolo

:- consult(tptp).
:- dynamic(step/3).
:- dynamic(defined/2).
:- dynamic(type/2).
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
literals(L | C, R) => R = [L | D], literals(C, D).
literals(S != T, R) => R = [~(S = T)].
literals(L, R) => R = [L].

% a formula turns out to be a clause
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
lp('$LIT'(N)) => format("ℓ~w", [N]).
lp('$LIT'(N)-_) => format("ℓ~w", [N]).
% named subformulae
lp('$FORM'(N)) => format("𝒻~w", [N]).
% references to input facts
% TODO clean this up wrt lp_app
lp('$INPUT'(Input)), getenv("GDV", _) => format("F.~w", [Input]).
lp('$INPUT'(Input)) => format("input_~w", [Input]).
lp('$INPUT'(Input, Args)), getenv("GDV", _) => format("(F.~w~@)", [Input, maplist(space_then_lp, Args)]).
lp('$INPUT'(Input, Args)) => format("(input_~w~@)", [Input, maplist(space_then_lp, Args)]).
lp('$CONJECTURE'(Input)) => format("vampire_conjecture_~w", [Input]).
% inference steps that failed to reconstruct for some reason
lp('$FAILED'(Step)) => format("begin { admit } end /* ~w */", [Step]).
% general terms
lp(T), nonvar(T) => T =.. [F|Args], lp_app(F, Args).

lp_app(F, []) => format("~@", lp_sym(F)).
lp_app(F, Args) => format("(~@~@)", [lp_sym(F), maplist(space_then_lp, Args)]).

lp_sym(F), getenv("GDV", _) => format("S.~w", [F]).
lp_sym(F) => format("~w", [F]).

% clauses
lp_clause([]) => format("π ⊥").
lp_clause([~L|C]) => format("π ~@ → ~@", [lp(L), lp_clause(C)]).
lp_clause([L|C]) => format("π ¬ ~@ → ~@", [lp(L), lp_clause(C)]).
lp_clause([], Lits) => lp_clause(Lits).
lp_clause([X|Xs], Lits) => format("Π ~@, ~@", [lp_binder(X), lp_clause(Xs, Lits)]).

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
apply_premise(P, Ts, Ls, Term) :-
  atom_concat(vampire_, P, F),
  append(Ts, Ls, Args), Term =.. [F|Args].

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

% ∨ₑ (input_butler_hates_poor x) nrxa (λ nlxhbx, ∨ₑ nlxhbx (λ nlx, nlx lx) nhbx);
disjunction_to_clause(Xs, Ls, Parent, ^Xs: ^Ls: (Subproof @ '$INPUT'(Parent, Xs))) :-
  disjunction_to_clause(0, Ls, Subproof).

/********************************************************************************
 * Proof printing
 ********************************************************************************/

print_input(_, _) :- getenv("GDV", _).
print_input(Name, Parent) :-
  \+ getenv("GDV", _),
  step(Name, F, input(_)),
  numbervars(F),
  format("constant symbol input_~w : π ~@;\n", [Parent, lp(F)]).

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
  format("opaque   symbol vampire_~w : ~@ ≔ ~@;\n", [Name, lp_clause(Xs, C), lp(Proof)]).

prove_clause(Name, Xs, Ls, input(Parent), Proof) =>
  disjunction_to_clause(Xs, Ls, Parent, Proof),
  print_input(Name, Parent).
prove_clause(_, _, _, cnf_transformation(Parent), Proof) =>
  Proof ='$FAILED'(cnf_transformation(Parent)),
  prove_formula(Parent).
prove_clause(_, Xs, Ls, sat_conversion(Parent), Proof) => variant(Xs, Ls, Parent, Proof).
prove_clause(_, Xs, Ls, avatar_contradiction_clause(Parent), Proof) => variant(Xs, Ls, Parent, Proof).
prove_clause(_, Xs, Ls, resolution(P1, P2), Proof) =>
  resolution(Xs, Ls, [P1, P2], Proof).
prove_clause(_, Xs, Ls, forward_subsumption_resolution(P1, P2), Proof) =>
  resolution(Xs, Ls, [P1, P2], Proof).
prove_clause(_, _, _, Record, Proof) =>
  Proof = '$FAILED'(Record),
  Record =.. [_|Parents],
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
prove_formula(_, F, negated_conjecture(Conjecture), Proof) =>
  step(Conjecture, _, input(Input)),
  Proof = '$CONJECTURE'(Input),
  numbervars(F),
  format("symbol ~@ : π ~@;\n", [lp('$CONJECTURE'(Input)), lp(F)]).
prove_formula(_, _, definition_folding(Parent, _), Proof) =>
  prove_formula(Parent),
  Proof = '$FAILED'(definition_folding(Parent, _)).

prove_formula(_, _, Record, Proof) =>
  Proof = '$FAILED'(Record),
  Record =.. [_|Parents],
  maplist(prove_formula, Parents).

/********************************************************************************
 * Preprocessing and the main loop
 ********************************************************************************/

% transform various proof records into an appropriate unified record
process_inference(file(_, Name), input(Name)).
process_inference(introduced(definition, _, [Record]), Record).
process_inference(inference(Rule, _, Premises), Record) :- Record =.. [Rule|Premises].

% try and work out how a predicate is defined
definition(!_: (F | ~D), P, Def) => P = D, Def = F.

% trap definitions, these need to be handled separately
add_definitions(F, introduced(definition, [new_symbols(naming,[P])], [predicate_definition_introduction])) =>
  definition(F, Px, Def),
  Px =.. [P|_],
  assert(defined(P, Def)).
add_definitions(_, _) => true.

% insert proof steps into our own records as step(Name, Formula, Record) triples
load(Name, Formula, Inference) =>
  % add any definitions that may be required
  add_definitions(Formula, Inference),
  % clean up a bit
  process_inference(Inference, Record),
  % insert a step(...) into the database
  assert(step(Name, Formula, Record)),
  % for any undeclared symbols in the formula, give them the default type
  forall(contains_function(F/N, Formula), ensure_typed(τ(ι), F, N)),
  forall(contains_predicate(P/N, Formula), ensure_typed(ο, P, N)).

load(end_of_file) :- !.
% type declaration stored in TPTP syntax
% implicit $i types resolved later
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

print_prelude :-
  getenv("GDV", _),
  print_lemmas.
print_prelude :-
  \+ getenv("GDV", _),
  print_lemmas,
  forall(type(Name, Type), format("constant symbol ~w : ~@;\n", [Name, lp(Type)])),
  nl.


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

main :-
  set_prolog_flag(occurs_check, true),
  % load the proof into `input` tuples in the Prolog database
  load_all,
  % based on this, print a prelude
  print_prelude,
  % then find falsum
  step(Name, $false, _), !, % cut: exactly one falsum will do
  prove_clause(Name).

:- initialization(main, main).
