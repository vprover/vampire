%prolog

:- consult(tptp).
:- dynamic(step/3).
:- dynamic(type/2).
:- dynamic(proved/1).

/********************************************************************************
 * utility predicates
 ********************************************************************************/

% a literal is negative with a certain atom
negation(~P, Q) => Q = P.
negation(L != R, Q) => Q = (L = R).
negation(_, _) => fail.

% the atom of a literal has a certain atom
literal_atom(~P, A) => A = P.
literal_atom(L != R, A) => A = (L = R).
literal_atom(L, A) => L = A.

% does a formula contain an atom?
contains_atom(A, !_: F) => contains_atom(A, F).
contains_atom(A, ?_: F) => contains_atom(A, F).
contains_atom(A, F & G) => contains_atom(A, F) ; contains_atom(A, G).
contains_atom(A, F | G) => contains_atom(A, F) ; contains_atom(A, G).
contains_atom(A, F => G) => contains_atom(A, F) ; contains_atom(A, G).
contains_atom(A, ~F) => contains_atom(A, F).
contains_atom(A, L != R) => A = (L = R).
contains_atom(_, $false) => fail.
contains_atom(A, R) => R = A.
% TODO more cases

% does a clause contain a predicate p/n?
contains_predicate(P/N, Clause) :-
  contains_atom(Atom, Clause),
  Atom =.. [P|_],
  P \== (=), P \== (<=>),
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
literals(L | C, R) => R = [L | D], literals(C, D).
literals(L, R) => R = [L].

% a formula turns out to be a clause
formula_clause(!X: F, Y, C) => Y = X, literals(F, C).
formula_clause(F, Y, C) => Y = [], literals(F, C).

% consider both orientations of a literal on backtracking
symmetric(F, F, Premise, Premise).
symmetric(L = R, R = L, Premise, sym(Premise)).

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
lp(L | R) => format("(~@)", [lp_disj(L | R)]).
lp(L & R) => format("(~@)", [lp_conj(L & R)]).
lp(L => R) => format("(~@ ⇒ ~@)", [lp(L), lp(R)]).
lp(![]: F) => lp(F).
lp(![X|Xs]: F) => format("`∀ ~@, ~@", [lp_binder(X), lp(!Xs: F)]).
lp(?[]: F) => lp(F).
lp(?[X|Xs]: F) => format("`∃ ~@, ~@", [lp_binder(X), lp(?Xs: F)]).
lp(τ(X)) => format("τ ~@", [lp(X)]).
lp(Domain > Range) => format("~@ → ~@", [lp(Domain), lp(Range)]).
lp(X * Y) => format("~@ → ~@", [lp(X), lp(Y)]).
% sort annotations should be discarded in terms
lp(X : _) => lp(X).
% variables should be bound with Prolog numbervars first
lp('$VAR'(N)) => format("x~d", [N]).
% named literals
lp('$LIT'(N)) => format("l~w", [N]).
lp('$LIT'(N)-_) => format("l~w", [N]).
% references to input facts
lp('$INPUT'(Input)) => format("input_~w", [Input]).
% inference steps that failed to reconstruct for some reason
lp('$FAILED'(Step)) => format("begin { admit } end; // ~p", [Step]).
% general terms
lp(T), nonvar(T) =>
  T =.. [F|Args],
  ( Args == [], !, format("~w", [F])
  ; format("(~w~@)", [F, maplist(space_then_lp, Args)])).

% associative operators
lp_conj((L1 & L2) & R) => lp_conj(L1 | L2 | R).
lp_conj(L & R) => format("~@ ∧ ~@", [lp(L), lp_conj(R)]).
lp_conj(F) => lp(F).

% disjunctions
lp_disj((L1 | L2) | R) => lp_disj(L1 | L2 | R).
lp_disj(L | R) => format("~@ ∨ ~@", [lp(L), lp_disj(R)]).
lp_disj(F) => lp(F).

% clauses
lp_clause([]) => format("π ⊥").
lp_clause([L|C]) => format("π ¬ ~@ → ~@", [lp(L), lp_clause(C)]).
lp_clause([], Lits) => lp_clause(Lits).
lp_clause([X|Xs], Lits) => format("Π ~@, ~@", [lp_binder(X), lp_clause(Xs, Lits)]).

space_then_lp(T) :- format(" ~@", [lp(T)]).
lp_binder(X : S) => format("~@ : ~@", [lp(X), lp(S)]).
lp_binder(X) => format("~@ : τ ι", [lp(X)]).

/********************************************************************************
 * Proof reconstruction
 ********************************************************************************/

% give each literal in the body of a clause a name
enumerate_literals([], _, []).
enumerate_literals([H|T], N, ['$LIT'(N)-H|E]) :-
  M is N + 1,
  enumerate_literals(T, M, E).
enumerate_literals(Xs, R) :- enumerate_literals(Xs, 0, R).

% try to use available literals to dispatch a list of goals Qi (modulo symmetry)
% if this fails, call `Solve`
match_literals([], _, [], _).
match_literals([Q|Qs], Ls, [Term|R], Solve) :-
  symmetric(Q, Q2, N, Term),
  member(N-Q2, Ls),
  match_literals(Qs, Ls, R, Solve).
match_literals([Q|Qs], Ls, [Term|R], Solve) :-
  call(Solve, Q, Term),
  match_literals(Qs, Ls, R, Solve).

% fail to solve a goal
no_alternative(_, _) :- fail.

% apply instantiation Ts and literal proofs Ls to P for a proof Term
apply_premise(P, Ts, Ls, Term) :- append(Ts, Ls, Args), Term =.. [P|Args].

% use a literal in a proof, possible instantiating the premise
instantiate(N-K, L, Proof) :-
  symmetric(K, KSym, N, Proof),
  unify_with_occurs_check(L, KSym).

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
variant(Conclusion, Name, Proof) :-
  step(Name, !Xs: C, _),
  instantiation(C, Conclusion, Lits),
  apply_premise(Name, Xs, Lits, Proof).

/*
% figure out how to use the major premise in a resolution step
major_resolution([L|Rest], Conclusion, Minor, [LProof|RestProof]) :-
  member(K, Conclusion),
  instantiate(K, L, LProof),
  major_resolution(Rest, Conclusion, Minor, RestProof).
major_resolution([~L|Rest], Conclusion, Minor, [(^[Pivot]: MinorProof)|RestProof]) :-
  Pivot = '$LIT'(pivot),
  step(Minor, !Ys: D, _),
  instantiation(D, [Pivot-L|Conclusion], MinorLits),
  apply_premise(Minor, Ys, MinorLits, MinorProof),
  instantiation(Rest, Conclusion, RestProof).

resolution(Conclusion, Major, Minor, Proof) :-
  step(Major, !Xs: C, _),
  major_resolution(C, Conclusion, Minor, Lits),
  apply_premise(Major, Xs, Lits, Proof).

% consider using either premise as the main premise for resolution
resolution(D, [P1, P2], Proof) :- resolution(D, P1, P2, Proof).
resolution(D, [P1, P2], Proof) :- resolution(D, P2, P1, Proof).
*/

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

/********************************************************************************
 * Proof printing
 ********************************************************************************/

% reconstruct and print a single clausal proof step
prove_clause(Name) :- proved(Name), !.
prove_clause(Name) :-
  assert(proved(Name)),
  step(Name, F, Record),
  formula_clause(F, Xs, C),
  numbervars(Xs),
  enumerate_literals(C, Ls),
  prove_clause(Name, Xs, Ls, Record, Proof),
  format("symbol ~w : ~@ ≔ ~@;\n", [Name, lp_clause(Xs, C), lp(Proof)]).

prove_clause(Name, _, _, input(Input), Proof) =>
  Proof = '$FAILED'(input(Input)), % TODO CNF conversion
  step(Name, F, _),
  numbervars(F),
  format("symbol input_~w : π ~@;\n", [Input, lp(F)]).
prove_clause(_, _, _, cnf_transformation(Parent), Proof) =>
  Proof ='$FAILED'(cnf_transformation(Parent)),
  prove_formula(Parent).
prove_clause(_, _, _, Record, Proof) =>
  Proof = '$FAILED'(Record),
  Record =.. [_|Parents],
  maplist(prove_clause, Parents).

% reconstruct and print a single non-clausal proof step
prove_formula(Name) :- proved(Name), !.
prove_formula(Name) :-
  assert(proved(Name)),
  step(Name, F, Record),
  numbervars(F),
  prove_formula(Name, F, Record, Proof),
  format("symbol ~w : π ~@ ≔ ~@;\n", [Name, lp(F), lp(Proof)]).

prove_formula(_, _, input(Input), _), proved(Input) => true.
prove_formula(Name, _, input(Input), Proof) =>
  Proof = '$INPUT'(Input),
  step(Name, F, _),
  numbervars(F),
  format("symbol input_~w : π ~@;\n", [Input, lp(F)]).
prove_formula(_, _, negated_conjecture(Conjecture), Proof) =>
  step(Conjecture, F, input(Input)),
  Proof = '$INPUT'(Input),
  numbervars(F),
  format("symbol input_~w : π ¬ ~@;\n", [Input, lp(F)]).

prove_formula(_, _, Record, Proof) =>
  Proof = '$FAILED'(Record),
  Record =.. [_|Parents],
  maplist(prove_formula, Parents).

/********************************************************************************
 * Preprocessing and the main loop
 ********************************************************************************/

% transform various proof records into an appropriate unified record
process_inference(file(_, Name), input(Name)).
process_inference(inference(Rule, _, Premises), Record) :- Record =.. [Rule|Premises].

% insert proof steps into our own records as input(Name, Formula, Record) triples
load(Name, _, Formula, Inference) =>
  % clean up a bit
  process_inference(Inference, Record),
  % insert a step(...) into the database
  assert(step(Name, Formula, Record)),
  % for any undeclared symbols in the formula, give them the default type
  forall(contains_function(F/N, Formula), ensure_typed(τ(ι), F, N)),
  forall(contains_predicate(P/N, Formula), ensure_typed('Prop', P, N)).

load(end_of_file) :- !.
% type declaration stored in TPTP syntax
% implicit $i types resolved later
load(tff(_, type, F : T)) :- !, assert(type(F, T)), load_all.
load(tff(Name, Role, Formula, Record)) :- load(Name, Role, Formula, Record), load_all.
load(fof(Name, Role, Formula, Record)) :- load(Name, Role, Formula, Record), load_all.
load(cnf(Name, Role, Formula, Record)) :- load(Name, Role, Formula, Record), load_all.

% load everything available from stdin
load_all :-
  read(Atom),
  % load should call load_all again, except on EOF
  load(Atom).

print_prelude :-
  format("\
require open Stdlib.Set;
require open Stdlib.Prop;
require open Stdlib.FOL;
require open Stdlib.Eq;
// TODO should be provided by Set?
constant symbol ι: Set;

"),
  forall(type(Name, Type), format("symbol ~w : ~@;\n", [Name, lp(Type)])),
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
  step(Name, $false, _),
  prove_clause(Name).

:-initialization(main, main).
