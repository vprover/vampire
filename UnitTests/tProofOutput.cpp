/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include <optional>
#include <sstream>

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Output.hpp"
#include "Lib/ScopeGuard.hpp"
#include "Lib/SharedSet.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Shell/TPTPProofPrinter.hpp"
#include "Shell/Options.hpp"

using namespace Lib;
using namespace Shell::TPTPOutput;
using namespace Kernel;
using namespace Test;

TEST_FUN(stored_interleaved_owns_separator)
{
  std::string separator = ",";
  const auto values = Output::interleaved(separator, range(1, 4));
  separator = ";";
  std::ostringstream first, second;
  first << values;
  second << values;
  ASS_EQ(first.str(), "1,2,3");
  ASS_EQ(second.str(), first.str());

  const auto temporarySeparator = Output::interleaved(std::string(" | "), range(1, 3));
  std::ostringstream other;
  other << temporarySeparator;
  ASS_EQ(other.str(), "1 | 2");

  std::ostringstream edges;
  edges << '[' << Output::interleaved(',', range(0, 0)) << "] ["
      << Output::interleaved(',', range(1, 2)) << ']';
  ASS_EQ(edges.str(), "[] [1]");
}

TEST_FUN(bound_writer_owns_arguments_and_uses_destination)
{
  struct Writer {
    unsigned calls = 0;
    std::ostream& write(std::ostream& out, const std::string& value) {
      ++calls;
      return out << '[' << value << ']';
    }
  } writer;

  std::string argument = "original";
  const auto fragment = Output::deferredMember<&Writer::write>(&writer, argument);
  argument = "changed";
  ASS_EQ(writer.calls, 0);
  std::ostringstream first, second;
  auto& returned = first << fragment << '!';
  ASS(&returned == &first);
  second << fragment;
  ASS_EQ(first.str(), "[original]!");
  ASS_EQ(second.str(), "[original]");
  ASS_EQ(writer.calls, 2);
}

TEST_FUN(reference_kinds_and_inference_lists)
{
  std::ostringstream references;
  references << Reference{"f", 17} << ','
      << Reference{"s", 18} << ','
      << Reference{"f", 19, "_D"};
  ASS_EQ(references.str(), "f17,s18,f19_D");

  const auto parents = Output::interleaved(',', range(1u, 3u).map([](unsigned number) {
    return Reference{"f", number};
  }));
  const auto source = inferenceAnnotation(std::string("resolve"), Output::Nothing{}, parents);
  std::ostringstream first, second;
  first << source;
  second << source;
  ASS_EQ(first.str(), "inference(resolve,[],[f1,f2])");
  ASS_EQ(second.str(), first.str());

  std::ostringstream empty;
  empty << inferenceAnnotation("input", Output::Nothing{}, Output::Nothing{});
  ASS_EQ(empty.str(), "inference(input,[],[])");
}

TEST_FUN(parenthesized_references_lvalues_and_stores_rvalues)
{
  std::string text = "a";
  const auto referenced = parenthesized(text);
  text = "b";
  const auto stored = parenthesized(std::string("c"));
  std::ostringstream out;
  out << referenced << stored << parenthesized(Output::interleaved(',', range(1, 3)));
  ASS_EQ(out.str(), "(b)(c)(1,2)");
}

TEST_FUN(comma_separated_lists_and_mapped_lists)
{
  std::ostringstream out;
  out << commaSeparated(range(1, 4)) << ' ' << commaSeparated(range(1, 1)) << '|'
      << commaSeparated(range(1, 3), [](int number) { return Reference{"f", unsigned(number)}; });
  ASS_EQ(out.str(), "1,2,3 |f1,f2");
}

TEST_FUN(comma_separated_stream_writer)
{
  std::ostringstream out;
  out << commaSeparatedWith(range(1, 4), [](std::ostream& stream, int number) {
    stream << 'X' << number << " : sort";
  }) << '|' << commaSeparatedWith(range(1, 1), [](std::ostream& stream, int number) {
    stream << number;
  });
  ASS_EQ(out.str(), "X1 : sort,X2 : sort,X3 : sort|");
}

TEST_FUN(complete_proof_step_owns_nested_fragments)
{
  const auto source = introducedAnnotation("definition",
      newSymbolAnnotation("definition", std::string("p")), std::string("predicate_definition"));
  const auto step = proofStep(Reference{"f", 4, "_D"}, "definition",
      std::string("p <=> q"), source);

  std::ostringstream first, second;
  first << step;
  second << step;
  const auto expected = std::string(languageName(proofLanguage())) + "(f4_D,definition,(\n"
      "  p <=> q),\n  introduced(definition,[new_symbols(definition,[p])],[predicate_definition])).\n";
  ASS_EQ(first.str(), expected);
  ASS_EQ(second.str(), expected);
}

static std::string printSplittingComponent(Stack<Lit> literals, Literal* nameLiteral)
{
  auto component = clause(literals,
      NonspecificInference0(GoalAffinity::AXIOM, InferenceRule::GENERAL_SPLITTING_COMPONENT));
  auto store = InferenceStore::instance();
  store->recordSplittingNameLiteral(component, nameLiteral);
  auto previousProof = env.options->proof();
  env.options->setProof(Shell::Options::Proof::TPTP);
  std::ostringstream out;
  store->outputProof(out, component);
  env.options->setProof(previousProof);
  return out.str();
}

TEST_FUN(single_literal_splitting_definition)
{
  // Component clause: p(X0) | name(X0).
  // Definition body: ![X0] : (p(X0) <=> ~name(X0)); X0 is shared with the name.
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort})
  DECL_PRED(name, {sort})
  Literal* namingLiteral = name(x);
  auto output = printSplittingComponent({p(x), namingLiteral}, namingLiteral);
  ASS(output.find("(! [X0] : (p(X0) <=> ~name(X0)))") != std::string::npos);
}

TEST_FUN(splitting_definition_without_shared_variables)
{
  // Component clause: p(X0) | name, with a propositional naming literal.
  // Definition body: (![X0] : p(X0)) <=> ~name; X0 is local to the component.
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort})
  DECL_PRED(name, {})
  Literal* namingLiteral = name();
  auto output = printSplittingComponent({p(x), namingLiteral}, namingLiteral);
  ASS(output.find("(! [X0] : p(X0)) <=> ~name") != std::string::npos);
}

TEST_FUN(splitting_definition_preserves_literal_order_and_sorts_unique_variables)
{
  // Component clause: r(X0,X2) | p(X1) | r(X0,X2) | name(X0,X1).
  // Definition body: ![X0,X1] : ((![X2] : (r(X0,X2) | p(X1) | r(X0,X2))) <=> ~name(X0,X1)).
  // Bind each variable once, keep the repeated literal, and bind only X2 locally.
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort})
  DECL_PRED(r, {sort, sort})
  DECL_PRED(name, {sort, sort})
  Literal* namingLiteral = name(x, y);
  auto output = printSplittingComponent({r(x, z), p(y), r(x, z), namingLiteral}, namingLiteral);
  ASS(output.find("(! [X0,X1] : ((! [X2] : (r(X0,X2) | p(X1) | r(X0,X2))) <=> ~name(X0,X1)))")
      != std::string::npos);
}

static std::string expectedClause(const Clause* clause, Language language, const std::string& body)
{
  return std::string(languageName(language)) + "(u" + std::to_string(clause->number())
      + ",axiom,\n    " + body + ").\n";
}

TEST_FUN(symbol_declarations_honor_requested_language)
{
  DECL_PRED(typed_predicate, {AtomicSort::intSort()})
  for (Language language : {Language::TFF, Language::TCF, Language::THF}) {
    std::ostringstream out;
    auto& returned = out << Shell::TPTPPrinter::symbolDeclarations(language);
    ASS(&returned == &out);
    const std::string prefix = std::string(languageName(language)) + "(";
    const std::string declarations = out.str();
    ASS(!declarations.empty());
    std::istringstream lines(declarations);
    std::string line;
    while (std::getline(lines, line)) {
      ASS_EQ(line.substr(0, prefix.size()), prefix);
    }
    ASS(declarations.find("typed_predicate: $int > $o") != std::string::npos);
  }
}

TEST_FUN(symbol_declarations_auto_select_language)
{
  DECL_PRED(typed_predicate, {AtomicSort::intSort()})
  const bool previousHigherOrder = env.higherOrder();
  ScopeGuard restore([&] { env.setHigherOrder(previousHigherOrder); });
  for (bool higherOrder : {false, true}) {
    env.setHigherOrder(higherOrder);
    std::ostringstream automatic, explicitLanguage;
    automatic << Shell::TPTPPrinter::symbolDeclarations();
    explicitLanguage << Shell::TPTPPrinter::symbolDeclarations(
        higherOrder ? Language::THF : Language::TFF);
    ASS(!automatic.str().empty());
    ASS_EQ(automatic.str(), explicitLanguage.str());
  }
}

TEST_FUN(default_unit_and_proof_languages_share_environment_flags)
{
  auto individual = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(untyped, {individual})
  DECL_PRED(typed, {AtomicSort::intSort()})
  auto untypedClause = clause({untyped(x)}, FromInput(GoalAffinity::AXIOM));
  auto typedClause = clause({typed(x)}, FromInput(GoalAffinity::AXIOM));
  auto arrowSort = AtomicSort::arrowSort(individual, individual);
  DECL_VAR_SORTED(equalLeft, 0, arrowSort)
  DECL_VAR_SORTED(equalRight, 1, arrowSort)
  auto equality = equalLeft == equalRight;
  auto higherOrderClause = clause({equality}, FromInput(GoalAffinity::AXIOM));
  FormulaUnit formula(atom(untyped(x)), FromInput(GoalAffinity::AXIOM));

  struct Case { Clause* clause; Language clausal; Language formula; };
  for (const auto& test : {
      Case{untypedClause, Language::CNF, Language::FOF},
      Case{typedClause, Language::TCF, Language::TFF},
      Case{higherOrderClause, Language::THF, Language::THF}}) {
    Problem problem(UnitList::singleton(test.clause));
    env.setMainProblem(&problem);
    ASS_EQ(Shell::TPTPPrinter::outputLanguage(true), test.clausal);
    ASS_EQ(Shell::TPTPPrinter::unitLanguage(test.clause), test.clausal);
    ASS_EQ(Shell::TPTPPrinter::unitLanguage(&formula), test.formula);
    ASS_EQ(proofLanguage(), test.formula);
  }
}

TEST_FUN(typed_clause_prefix_sorts_variables_and_spells_out_sorts)
{
  // Clause: p(X1,X0), with both variables of sort $i.
  // TCF body: ![X0 : $i,X1 : $i] : (p(X1,X0)); CNF body: (p(X1,X0)).
  // Sort the prefix numerically without reordering the predicate's arguments.
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort, sort})
  auto cl = clause({p(y, x)}, FromInput(GoalAffinity::AXIOM));
  ASS_EQ(Shell::TPTPPrinter::toString(cl, Language::TCF, Role::AXIOM),
      expectedClause(cl, Language::TCF, "![X0 : $i,X1 : $i] : (p(X1,X0))"));
  ASS_EQ(Shell::TPTPPrinter::toString(cl, Language::CNF, Role::AXIOM),
      expectedClause(cl, Language::CNF, "(p(X1,X0))"));

  DECL_PRED(q, {AtomicSort::intSort(), sort})
  // Mixed-sort clause: q(X1:$int,X0:$i).
  // TCF body: ![X0 : $i,X1 : $int] : (q(X1,X0)).
  auto mixed = clause({q(y, x)}, FromInput(GoalAffinity::AXIOM));
  ASS_EQ(Shell::TPTPPrinter::toString(mixed, Language::TCF, Role::AXIOM),
      expectedClause(mixed, Language::TCF, "![X0 : $i,X1 : $int] : (q(X1,X0))"));
}

TEST_FUN(typed_clause_prefix_omits_ground_and_empty_quantifiers)
{
  // Ground clause p(a) prints the TCF body (p(a)), with no universal prefix.
  // The empty clause prints ($false), also without an empty ![] binder.
  auto sort = AtomicSort::defaultSort();
  DECL_CONST(a, sort)
  DECL_PRED(p, {sort})
  auto ground = clause({p(a)}, FromInput(GoalAffinity::AXIOM));
  ASS_EQ(Shell::TPTPPrinter::toString(ground, Language::TCF, Role::AXIOM),
      expectedClause(ground, Language::TCF, "(p(a))"));
  auto empty = clause(Stack<Lit>{}, FromInput(GoalAffinity::AXIOM));
  ASS_EQ(Shell::TPTPPrinter::toString(empty, Language::TCF, Role::AXIOM),
      expectedClause(empty, Language::TCF, "($false)"));
}

TEST_FUN(typed_clause_prefix_puts_type_variables_before_term_variables)
{
  // Polymorphic clause: p(X3,X0), where X3:$tType and X0:X3.
  // TCF body: ![X3 : $tType,X0 : X3] : (p(X3,X0)).
  // Bind the type before its term variable, despite X0 having the smaller number.
  PredSugar p("p", {SortSugar(TermList::var(101))}, 1);
  SortSugar type(TermList::var(3));
  TermSugar term(TermList::var(0), type);
  auto cl = clause({p(type, term)}, FromInput(GoalAffinity::AXIOM));
  ASS_EQ(Shell::TPTPPrinter::toString(cl, Language::TCF, Role::AXIOM),
      expectedClause(cl, Language::TCF, "![X3 : $tType,X0 : X3] : (p(X3,X0))"));
}

TEST_FUN(typed_clause_prefix_sorts_multiple_type_variables)
{
  // Polymorphic clause: p(X3,X2,X0,X1), with X0:X3 and X1:X2.
  // TCF body: ![X2 : $tType,X3 : $tType,X0 : X3,X1 : X2] : (p(X3,X2,X0,X1)).
  // Sort type and term variables separately; preserve the literal's argument order.
  PredSugar p("p", {SortSugar(TermList::var(101)), SortSugar(TermList::var(102))}, 2);
  SortSugar a(TermList::var(3));
  SortSugar b(TermList::var(2));
  TermSugar x(TermList::var(0), a);
  TermSugar y(TermList::var(1), b);
  auto cl = clause({p(a, b, x, y)}, FromInput(GoalAffinity::AXIOM));
  ASS_EQ(Shell::TPTPPrinter::toString(cl, Language::TCF, Role::AXIOM),
      expectedClause(cl, Language::TCF,
          "![X2 : $tType,X3 : $tType,X0 : X3,X1 : X2] : (p(X3,X2,X0,X1))"));
}

TEST_FUN(universal_closure_binds_only_free_variables)
{
  // Formula: ![X0] : p(X0,X1), with X1 free.
  // FOF closure: ![X1] : (![X0] : p(X0,X1)); do not bind X0 again outside.
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort, sort})
  DECL_VAR_SORTED(x0, 0, sort)
  auto formula = forall(x0, atom(p(x0, y)));
  FormulaUnit unit(formula, FromInput(GoalAffinity::AXIOM));
  std::ostringstream out;
  out << universalClosure(&unit, Language::FOF);
  ASS_EQ(out.str(), "(! [X1] : (! [X0] : p(X0,X1)))");
}

TEST_FUN(universal_closure_uses_target_language_for_variable_annotations)
{
  // Clause: p(X1,X0), with both variables of sort $i.
  // FOF closure: ![X0,X1] : (p(X1,X0)).
  // TFF/THF/TCF closure: ![X0 : $i,X1 : $i] : (p(X1,X0)).
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort, sort})
  auto cl = clause({p(y, x)}, FromInput(GoalAffinity::AXIOM));
  std::ostringstream fof;
  fof << universalClosure(cl, Language::FOF);
  ASS_EQ(fof.str(), "(! [X0,X1] : (p(X1,X0)))");
  for (auto language : {Language::TFF, Language::THF, Language::TCF}) {
    std::ostringstream typed;
    typed << universalClosure(cl, language);
    ASS_EQ(typed.str(), "(! [X0 : $i,X1 : $i] : (p(X1,X0)))");
  }
}

TEST_FUN(typed_quantifiers_share_type_variable_order_across_languages)
{
  // Clause: p(X3,X2,X0,X1), with X0:X3 and X1:X2.
  // Print only the binding list, identically for TFF, THF and TCF:
  // X2 : $tType,X3 : $tType,X0 : X3,X1 : X2.
  PredSugar p("p", {SortSugar(TermList::var(101)), SortSugar(TermList::var(102))}, 2);
  SortSugar a(TermList::var(3));
  SortSugar b(TermList::var(2));
  TermSugar x(TermList::var(0), a);
  TermSugar y(TermList::var(1), b);
  auto cl = clause({p(a, b, x, y)}, FromInput(GoalAffinity::AXIOM));
  for (auto language : {Language::TFF, Language::THF, Language::TCF}) {
    std::ostringstream out;
    out << QuantifiedVariables(cl, language);
    ASS_EQ(out.str(), "X2 : $tType,X3 : $tType,X0 : X3,X1 : X2");
  }
}

TEST_FUN(thf_quantifiers_parenthesize_arrow_sorts)
{
  // Bind X0 of function type $i > $i; the THF binding must print X0 : ($i > $i).
  DHMap<unsigned, TermList, FnvHash, IdentityHash> sorts;
  sorts.insert(0, AtomicSort::arrowSort(AtomicSort::defaultSort(), AtomicSort::defaultSort()));
  std::ostringstream out;
  out << QuantifiedVariables(pvi(range(0u, 1u)), sorts, Language::THF);
  ASS_EQ(out.str(), "X0 : $i > $i");
}

TEST_FUN(thf_closure_does_not_rebind_lambda_variables)
{
  // Formula: (^[X0:$i] : X0) = X1, where X1 has type $i > $i.
  // Print only X1 : ($i > $i); X0 is already bound by the lambda.
  auto sort = AtomicSort::defaultSort();
  auto arrowSort = AtomicSort::arrowSort(sort, sort);
  auto lambda = Term::createLambda(TermList::var(0), VSList::singleton({0, sort}), sort);
  auto equality = Literal::createEquality(true, TermList(lambda), TermList::var(1), arrowSort);
  FormulaUnit unit(atom(equality), FromInput(GoalAffinity::AXIOM));
  std::ostringstream out;
  out << QuantifiedVariables(&unit, Language::THF);
  ASS_EQ(out.str(), "X1 : $i > $i");
}

static void checkFormulaOutput(const Formula* formula, const std::string& expected)
{
  ASS_EQ(Shell::TPTPPrinter::toString(formula), expected);
  std::ostringstream out;
  out << "before:";
  auto& returned = out << Shell::TPTPPrinter::formula(formula);
  ASS(&returned == &out);
  returned << ":after";
  ASS_EQ(out.str(), "before:" + expected + ":after");
}

TEST_FUN(formula_stream_preserves_connectives_and_argument_order)
{
  DECL_PRED(p, {})
  DECL_PRED(q, {})
  auto left = atom(p());
  auto right = atom(q());
  checkFormulaOutput(left, "p");
  checkFormulaOutput(~left, "(~ p)");
  checkFormulaOutput(impl(left, right), "(p => q)");
  checkFormulaOutput(equiv(left, right), "(p <=> q)");
  checkFormulaOutput(xorr(left, right), "(p <~> q)");
  checkFormulaOutput(conj({right, left}), "(q & p)");
  checkFormulaOutput(disj({right, left}), "(q | p)");
  checkFormulaOutput(trueF(), "$true");
  checkFormulaOutput(falseF(), "$false");
}

TEST_FUN(formula_stream_preserves_quantifier_sorts_and_spacing)
{
  DECL_PRED(p, {})
  DECL_VAR_SORTED(x2, 2, AtomicSort::defaultSort())
  auto atomP = atom(p());
  auto vars = VSList::cons({0, AtomicSort::defaultSort()},
      VSList::singleton({1, AtomicSort::intSort()}));
  checkFormulaOutput(new QuantifiedFormula(FORALL, vars, atomP),
      "(! [X0, X1 : $int] : p)");
  auto existential = exists(x2, atomP);
  checkFormulaOutput(existential, "(? [X2] : p)");
  checkFormulaOutput(new QuantifiedFormula(FORALL, vars, existential),
      "(! [X0, X1 : $int] : ? [X2] : p)");
}

TEST_FUN(formula_stream_preserves_equality_parentheses_and_boolean_terms)
{
  auto sort = AtomicSort::defaultSort();
  DECL_VAR_SORTED(left, 0, sort)
  DECL_VAR_SORTED(right, 1, sort)
  DECL_VAR(x2, 2)
  checkFormulaOutput(atom(left == right), "(X0 = X1)");
  checkFormulaOutput(atom(left != right), "(X0 != X1)");
  checkFormulaOutput(boolT(x2), "X2");
}

TEST_FUN(thf_unit_output_parenthesizes_applications_and_annotates_binders)
{
  const bool previousHigherOrder = env.higherOrder();
  const auto previousPrinting = env.options->holPrinting();
  ScopeGuard restore([&] {
    env.setHigherOrder(previousHigherOrder);
    env.options->setHolPrinting(previousPrinting);
  });
  env.setHigherOrder(true);
  env.options->setHolPrinting(Shell::Options::HPrinting::TPTP);

  auto sort = AtomicSort::boolSort();
  DECL_CONST(p, sort)
  DECL_CONST(f, arrow(sort, sort))
  DECL_CONST(x, sort)
  auto application = boolT(ap(f(), x()));
  auto formula = conj({application, boolT(p())});
  checkFormulaOutput(formula, "((f @ x) & p)");
  // Proof bodies use Formula::toString; both renderers must preserve application parentheses.
  Formula* formulaPtr = formula;
  ASS_EQ(formulaPtr->toString(/*mightNeedParens=*/true), Shell::TPTPPrinter::toString(formulaPtr));
  FormulaUnit unit(formulaPtr, FromInput(GoalAffinity::AXIOM));
  ASS_EQ(Shell::TPTPPrinter::toString(&unit, Language::THF, Role::AXIOM),
      "thf(u" + std::to_string(unit.number()) + ",axiom,\n    ((f @ x) & p)).\n");

  DECL_VAR_SORTED(x0, 0, AtomicSort::defaultSort())
  auto universal = forall(x0, boolT(p()));
  checkFormulaOutput(universal, "(! [X0 : $i] : p)");
}

TEST_FUN(formula_stream_handles_deep_nesting_iteratively)
{
  DECL_PRED(p, {})
  auto formula = atom(p());
  const unsigned depth = 10000;
  std::string expected = "(";
  expected.reserve(4 * depth + 1);
  for (unsigned i = 0; i < depth; ++i) {
    formula = ~formula;
    expected += "~ ";
  }
  expected += "p)";
  checkFormulaOutput(formula, expected);
}

// unit() prints the role plain, whatever the goal affinity: the role is up to namedUnit()'s caller.
static void checkUnitOutput(const Unit* unit, const std::string& prefix, const std::string& body,
    std::optional<Language> language = std::nullopt)
{
  auto expected = prefix + "(u" + std::to_string(unit->number()) + ",plain,\n    " + body + ").\n";
  Language printed = language.value_or(Shell::TPTPPrinter::unitLanguage(unit));
  ASS_EQ(Shell::TPTPPrinter::toString(unit, printed), expected);
  if (!language) {
    ASS_EQ(Shell::TPTPPrinter::toString(unit), expected);
  }
  std::ostringstream out;
  out << "before:";
  auto& returned = out << Shell::TPTPPrinter::unit(unit, printed);
  ASS(&returned == &out);
  returned << ":after";
  ASS_EQ(out.str(), "before:" + expected + ":after");
}

// Like the parser: the stated conjecture is an input unit, and the prover works on a unit
// derived from it by negation, which inherits the goal affinity CONJECTURE.
static Inference fromNegatedConjecture(Unit* stated)
{ return FormulaClauseTransformation(InferenceRule::CONJECTURE_NEGATION, stated); }

TEST_FUN(unit_stream_prints_plain_role)
{
  DECL_PRED(p, {})
  auto pAtom = atom(p());
  FormulaUnit axiom(pAtom, FromInput(GoalAffinity::AXIOM));
  checkUnitOutput(&axiom, "fof", "p");
  checkUnitOutput(&axiom, "tff", "p", Language::TFF);
  FormulaUnit stated(pAtom, FromInput(GoalAffinity::CONJECTURE));
  checkUnitOutput(&stated, "fof", "p");
  FormulaUnit negated(~pAtom, fromNegatedConjecture(&stated));
  checkUnitOutput(&negated, "fof", "(~ p)");
}

TEST_FUN(unit_stream_uses_given_role)
{
  DECL_PRED(p, {})
  FormulaUnit axiom(atom(p()), FromInput(GoalAffinity::AXIOM));
  auto expected = "fof(u" + std::to_string(axiom.number()) + ",axiom,\n    p).\n";
  ASS_EQ(Shell::TPTPPrinter::toString(&axiom, Language::FOF, "axiom"), expected);
  std::ostringstream out;
  out << Shell::TPTPPrinter::unit(&axiom, Language::FOF, "axiom");
  ASS_EQ(out.str(), expected);
}

TEST_FUN(unit_stream_preserves_clause_order)
{
  // Clause: p | q. Print cnf(uN,plain,(p | q)) or tcf(uN,plain,(p | q)).
  // uN is the generated unit name; the ground clause needs no variable prefix.
  DECL_PRED(p, {})
  DECL_PRED(q, {})
  auto cl = clause({p(), q()}, FromInput(GoalAffinity::AXIOM));
  checkUnitOutput(cl, "cnf", "(p | q)");
  checkUnitOutput(cl, "tcf", "(p | q)", Language::TCF);
}

static std::string printNamedUnit(const char* name, const char* role, Unit* unit,
    bool includeSplitLevels = false, Language language = Language::TCF)
{
  std::ostringstream out;
  out << Shell::TPTPPrinter::namedUnit(unit, name, role, language, includeSplitLevels);
  return out.str();
}

TEST_FUN(named_unit_stream_uses_given_name_and_role)
{
  // Clause: p(X0) | q. With name c and role claim, print:
  // tcf(c,claim, ![X0 : $i] : (p(X0) | q)).
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort})
  DECL_PRED(q, {})
  auto pOrQ = clause({p(x), q()}, FromInput(GoalAffinity::AXIOM));
  ASS_EQ(printNamedUnit("c", "claim", pOrQ), "tcf(c,claim,\n    ![X0 : $i] : (p(X0) | q)).\n");

  // Clause: p(X0), under split levels 3 and 4. With split-level output enabled:
  // tcf(s,claim, ![X0 : $i] : (p(X0) | $splitLevel3 | $splitLevel4)).
  // With it disabled: tcf(s,claim, ![X0 : $i] : (p(X0))).
  auto split = clause({p(x)}, FromInput(GoalAffinity::AXIOM));
  split->setSplits(SplitSet::getRange(3, 5));
  ASS_EQ(printNamedUnit("s", "claim", split, true),
      "tcf(s,claim,\n    ![X0 : $i] : (p(X0) | $splitLevel3 | $splitLevel4)).\n");
  ASS_EQ(printNamedUnit("s", "claim", split), "tcf(s,claim,\n    ![X0 : $i] : (p(X0))).\n");

  // The role is the caller's, whatever the goal affinity of the unit.
  FormulaUnit stated(atom(q()), FromInput(GoalAffinity::CONJECTURE));
  FormulaUnit negated(~atom(q()), fromNegatedConjecture(&stated));
  ASS_EQ(printNamedUnit("f", "conjecture", &negated, false, Language::TFF),
      "tff(f,conjecture,\n    (~ q)).\n");
}

TEST_FUN(inference_rule_names_are_identifiers)
{
  for (std::underlying_type_t<InferenceRule> i = 0; i < toNumber(InferenceRule::GENERIC_THEORY_AXIOM_LAST); i++) {
    try {
      std::string res = ruleName(static_cast<InferenceRule>(i));
      ASS_REP(res.size(), "rule name is empty");
      ASS_REP(std::islower(res[0]), "rule name first character is not lowercase letter: " + res);
      for (const auto& c : res) {
        ASS_REP(std::isalnum(c) || c == '_', "rule name has non-[a-zA-Z0-9_] characters: " + res);
      }
    } catch (InvalidOperationException e) { ASS_EQ(e.msg(), "invalid inference rule"); }
  }
}