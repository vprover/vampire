/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include <sstream>

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Output.hpp"
#include "Lib/ScopeGuard.hpp"
#include "Lib/SharedSet.hpp"
#include "Kernel/Formula.hpp"
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

static std::string printSplittingComponent(Stack<Literal*> literals, Literal* nameLiteral)
{
  auto component = Clause::fromStack(literals,
      NonspecificInference0(UnitInputType::AXIOM, InferenceRule::GENERAL_SPLITTING_COMPONENT));
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
  ASS(output.find("( ! [X0] : (p(X0) <=> ~name(X0)) )") != std::string::npos);
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
  ASS(output.find("( ! [X0] : p(X0) ) <=> ~name") != std::string::npos);
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
  ASS(output.find("( ! [X0,X1] : (( ! [X2] : (r(X0,X2) | p(X1) | r(X0,X2)) ) <=> ~name(X0,X1)) )")
      != std::string::npos);
}

static std::string expectedClause(const Clause* clause, bool typed, const std::string& body)
{
  return std::string(typed ? "tcf" : "cnf") + "(u" + std::to_string(clause->number())
      + ",axiom,\n    " + body + ").\n";
}

TEST_FUN(typed_clause_prefix_sorts_variables_and_spells_out_sorts)
{
  // Clause: p(X1,X0), with both variables of sort $i.
  // TCF body: ![X0 : $i,X1 : $i] : ( p(X1,X0) ); CNF body: ( p(X1,X0) ).
  // Sort the prefix numerically without reordering the predicate's arguments.
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort, sort})
  auto clause = Clause::fromLiterals({p(y, x)}, FromInput(UnitInputType::AXIOM));
  ASS_EQ(Shell::TPTPPrinter::toString(clause, true),
      expectedClause(clause, true, "![X0 : $i,X1 : $i] : ( p(X1,X0) )"));
  ASS_EQ(Shell::TPTPPrinter::toString(clause, false),
      expectedClause(clause, false, "( p(X1,X0) )"));

  DECL_PRED(q, {AtomicSort::intSort(), sort})
  // Mixed-sort clause: q(X1:$int,X0:$i).
  // TCF body: ![X0 : $i,X1 : $int] : ( q(X1,X0) ).
  auto mixed = Clause::fromLiterals({q(y, x)}, FromInput(UnitInputType::AXIOM));
  ASS_EQ(Shell::TPTPPrinter::toString(mixed, true),
      expectedClause(mixed, true, "![X0 : $i,X1 : $int] : ( q(X1,X0) )"));
}

TEST_FUN(typed_clause_prefix_omits_ground_and_empty_quantifiers)
{
  // Ground clause p(a) prints the TCF body ( p(a) ), with no universal prefix.
  // The empty clause prints ( $false ), also without an empty ![] binder.
  auto sort = AtomicSort::defaultSort();
  DECL_CONST(a, sort)
  DECL_PRED(p, {sort})
  auto ground = Clause::fromLiterals({p(a)}, FromInput(UnitInputType::AXIOM));
  ASS_EQ(Shell::TPTPPrinter::toString(ground, true),
      expectedClause(ground, true, "( p(a) )"));
  auto empty = Clause::fromLiterals({}, FromInput(UnitInputType::AXIOM));
  ASS_EQ(Shell::TPTPPrinter::toString(empty, true),
      expectedClause(empty, true, "( $false )"));
}

TEST_FUN(typed_clause_prefix_puts_type_variables_before_term_variables)
{
  // Polymorphic clause: p(X3,X0), where X3:$tType and X0:X3.
  // TCF body: ![X3 : $tType,X0 : X3] : ( p(X3,X0) ).
  // Bind the type before its term variable, despite X0 having the smaller number.
  PredSugar p("p", {SortSugar(TermList::var(101))}, 1);
  SortSugar type(TermList::var(3));
  TermSugar term(TermList::var(0), type);
  auto clause = Clause::fromLiterals({p(type, term)}, FromInput(UnitInputType::AXIOM));
  ASS_EQ(Shell::TPTPPrinter::toString(clause, true),
      expectedClause(clause, true, "![X3 : $tType,X0 : X3] : ( p(X3,X0) )"));
}

TEST_FUN(typed_clause_prefix_sorts_multiple_type_variables)
{
  // Polymorphic clause: p(X3,X2,X0,X1), with X0:X3 and X1:X2.
  // TCF body: ![X2 : $tType,X3 : $tType,X0 : X3,X1 : X2] : ( p(X3,X2,X0,X1) ).
  // Sort type and term variables separately; preserve the literal's argument order.
  PredSugar p("p", {SortSugar(TermList::var(101)), SortSugar(TermList::var(102))}, 2);
  SortSugar a(TermList::var(3));
  SortSugar b(TermList::var(2));
  TermSugar x(TermList::var(0), a);
  TermSugar y(TermList::var(1), b);
  auto clause = Clause::fromLiterals({p(a, b, x, y)}, FromInput(UnitInputType::AXIOM));
  ASS_EQ(Shell::TPTPPrinter::toString(clause, true),
      expectedClause(clause, true,
          "![X2 : $tType,X3 : $tType,X0 : X3,X1 : X2] : ( p(X3,X2,X0,X1) )"));
}

TEST_FUN(universal_closure_binds_only_free_variables)
{
  // Formula: ![X0] : p(X0,X1), with X1 free.
  // FOF closure: ![X1] : (![X0] : p(X0,X1)); do not bind X0 again outside.
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort, sort})
  auto formula = new QuantifiedFormula(FORALL, VSList::singleton({0, sort}),
      new AtomicFormula(p(x, y)));
  FormulaUnit unit(formula, FromInput(UnitInputType::AXIOM));
  std::ostringstream out;
  out << universalClosure(&unit, Language::FOF);
  ASS_EQ(out.str(), "( ! [X1] : (! [X0] : p(X0,X1)) )");
}

TEST_FUN(universal_closure_uses_target_language_for_variable_annotations)
{
  // Clause: p(X1,X0), with both variables of sort $i.
  // FOF closure: ![X0,X1] : (p(X1,X0)).
  // TFF/THF/TCF closure: ![X0 : $i,X1 : $i] : (p(X1,X0)).
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort, sort})
  auto clause = Clause::fromLiterals({p(y, x)}, FromInput(UnitInputType::AXIOM));
  std::ostringstream fof;
  fof << universalClosure(clause, Language::FOF);
  ASS_EQ(fof.str(), "( ! [X0,X1] : (p(X1,X0)) )");
  for (auto language : {Language::TFF, Language::THF, Language::TCF}) {
    std::ostringstream typed;
    typed << universalClosure(clause, language);
    ASS_EQ(typed.str(), "( ! [X0 : $i,X1 : $i] : (p(X1,X0)) )");
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
  auto clause = Clause::fromLiterals({p(a, b, x, y)}, FromInput(UnitInputType::AXIOM));
  for (auto language : {Language::TFF, Language::THF, Language::TCF}) {
    std::ostringstream out;
    out << QuantifiedVariables(clause, language);
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
  ASS_EQ(out.str(), "X0 : ($i > $i)");
}

TEST_FUN(thf_closure_does_not_rebind_lambda_variables)
{
  // Formula: (^[X0:$i] : X0) = X1, where X1 has type $i > $i.
  // Print only X1 : ($i > $i); X0 is already bound by the lambda.
  auto sort = AtomicSort::defaultSort();
  auto arrowSort = AtomicSort::arrowSort(sort, sort);
  auto lambda = Term::createLambda(TermList::var(0), VSList::singleton({0, sort}), sort);
  auto equality = Literal::createEquality(true, TermList(lambda), TermList::var(1), arrowSort);
  FormulaUnit unit(new AtomicFormula(equality), FromInput(UnitInputType::AXIOM));
  std::ostringstream out;
  out << QuantifiedVariables(&unit, Language::THF);
  ASS_EQ(out.str(), "X1 : ($i > $i)");
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
  auto left = new AtomicFormula(p());
  auto right = new AtomicFormula(q());
  checkFormulaOutput(left, "p");
  checkFormulaOutput(new NegatedFormula(left), "(~ p)");
  checkFormulaOutput(new BinaryFormula(IMP, left, right), "(p => q)");
  checkFormulaOutput(new BinaryFormula(IFF, left, right), "(p <=> q)");
  checkFormulaOutput(new BinaryFormula(XOR, left, right), "(p <~> q)");
  auto args = FormulaList::cons(left, FormulaList::singleton(right));
  checkFormulaOutput(new JunctionFormula(AND, args), "(q & p)");
  checkFormulaOutput(new JunctionFormula(OR, args), "(q | p)");
  checkFormulaOutput(Formula::trueFormula(), "$true");
  checkFormulaOutput(Formula::falseFormula(), "$false");
}

TEST_FUN(formula_stream_preserves_quantifier_sorts_and_spacing)
{
  DECL_PRED(p, {})
  auto atom = new AtomicFormula(p());
  auto vars = VSList::cons({0, AtomicSort::defaultSort()},
      VSList::singleton({1, AtomicSort::intSort()}));
  checkFormulaOutput(new QuantifiedFormula(FORALL, vars, atom),
      "(![X0, X1 : $int] : (p))");
  auto existential = new QuantifiedFormula(EXISTS,
      VSList::singleton({2, AtomicSort::defaultSort()}), atom);
  checkFormulaOutput(existential, "(?[X2] : (p))");
  checkFormulaOutput(new QuantifiedFormula(FORALL, vars, existential),
      "(![X0, X1 : $int] : ((?[X2] : (p))))");
}

TEST_FUN(formula_stream_preserves_equality_parentheses_and_boolean_terms)
{
  auto sort = AtomicSort::defaultSort();
  auto left = TermList::var(0);
  auto right = TermList::var(1);
  checkFormulaOutput(new AtomicFormula(Literal::createEquality(true, left, right, sort)),
      "(X0 = X1)");
  checkFormulaOutput(new AtomicFormula(Literal::createEquality(false, left, right, sort)),
      "(X0 != X1)");
  checkFormulaOutput(new BoolTermFormula(TermList::var(2)), "X2");
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
  auto application = new BoolTermFormula(ap(f(), x()));
  auto formula = new JunctionFormula(AND,
      FormulaList::cons(new BoolTermFormula(p()), FormulaList::singleton(application)));
  checkFormulaOutput(formula, "((f @ x) & p)");
  // Proof bodies use Formula::toString; both renderers must preserve application parentheses.
  ASS_EQ(formula->toString(false), Shell::TPTPPrinter::toString(formula));
  FormulaUnit unit(formula, FromInput(UnitInputType::AXIOM));
  ASS_EQ(Shell::TPTPPrinter::toString(&unit),
      "thf(u" + std::to_string(unit.number()) + ",axiom,\n    ((f @ x) & p)).\n");

  auto universal = new QuantifiedFormula(FORALL,
      VSList::singleton({0, AtomicSort::defaultSort()}), new BoolTermFormula(p()));
  checkFormulaOutput(universal, "(![X0 : $i] : (p))");
}

TEST_FUN(formula_stream_handles_deep_nesting_iteratively)
{
  DECL_PRED(p, {})
  Formula* formula = new AtomicFormula(p());
  const unsigned depth = 10000;
  std::string expected;
  expected.reserve(4 * depth + 1);
  for (unsigned i = 0; i < depth; ++i) {
    formula = new NegatedFormula(formula);
    expected += "(~ ";
  }
  expected += 'p';
  expected.append(depth, ')');
  checkFormulaOutput(formula, expected);
}

static void checkUnitOutput(const Unit* unit, const std::string& prefix, const std::string& role,
    const std::string& body, bool typedClauses = false)
{
  auto expected = prefix + "(u" + std::to_string(unit->number()) + ',' + role + ",\n    " + body + ").\n";
  ASS_EQ(Shell::TPTPPrinter::toString(unit, typedClauses), expected);
  std::ostringstream out;
  out << "before:";
  auto& returned = out << Shell::TPTPPrinter::unit(unit, typedClauses);
  ASS(&returned == &out);
  returned << ":after";
  ASS_EQ(out.str(), "before:" + expected + ":after");
}

TEST_FUN(unit_stream_preserves_formula_roles)
{
  DECL_PRED(p, {})
  auto atom = new AtomicFormula(p());
  FormulaUnit axiom(atom, FromInput(UnitInputType::AXIOM));
  checkUnitOutput(&axiom, "tff", "axiom", "p");
  checkUnitOutput(&axiom, "tff", "axiom", "p", true);
  FormulaUnit assumption(atom, FromInput(UnitInputType::ASSUMPTION));
  checkUnitOutput(&assumption, "tff", "hypothesis", "p");
  FormulaUnit extensionality(atom, FromInput(UnitInputType::EXTENSIONALITY_AXIOM));
  checkUnitOutput(&extensionality, "tff", "extensionality", "p");
  FormulaUnit negatedConjecture(atom, FromInput(UnitInputType::NEGATED_CONJECTURE));
  checkUnitOutput(&negatedConjecture, "tff", "negated_conjecture", "p");
}

// Like the parser: the stated conjecture is an input unit, and the prover works on a unit
// derived from it by negation, which inherits the input type CONJECTURE.
static Inference fromNegatedConjecture(Unit* stated)
{ return FormulaClauseTransformation(InferenceRule::NEGATED_CONJECTURE, stated); }

TEST_FUN(conjecture_relation_distinguishes_stated_and_negated_conjectures)
{
  // The final clause is p, derived from negating a stated conjecture.
  // No text is printed here: its relation must be NEGATED_CONJECTURE, even
  // though its inherited input type is CONJECTURE (as for the negated formula).
  DECL_PRED(p, {})
  auto atom = new AtomicFormula(p());
  FormulaUnit axiom(atom, FromInput(UnitInputType::AXIOM));
  ASS(axiom.conjectureRelation() == ConjectureRelation::NONE);
  FormulaUnit stated(atom, FromInput(UnitInputType::CONJECTURE));
  ASS(stated.conjectureRelation() == ConjectureRelation::CONJECTURE);
  FormulaUnit negated(new NegatedFormula(atom), fromNegatedConjecture(&stated));
  ASS(negated.conjectureRelation() == ConjectureRelation::NEGATED_FORMULA);
  FormulaUnit given(atom, FromInput(UnitInputType::NEGATED_CONJECTURE));
  ASS(given.conjectureRelation() == ConjectureRelation::NEGATED_CONJECTURE);
  auto clause = Clause::fromLiterals({p()}, fromNegatedConjecture(&stated));
  ASS(clause->conjectureRelation() == ConjectureRelation::NEGATED_CONJECTURE);
}

TEST_FUN(unit_stream_prints_stated_conjecture_unchanged)
{
  DECL_PRED(p, {})
  FormulaUnit stated(new AtomicFormula(p()), FromInput(UnitInputType::CONJECTURE));
  checkUnitOutput(&stated, "tff", "conjecture", "p");
}

TEST_FUN(unit_stream_preserves_conjecture_negation_cases)
{
  DECL_PRED(p, {})
  auto atom = new AtomicFormula(p());
  FormulaUnit stated(atom, FromInput(UnitInputType::CONJECTURE));
  FormulaUnit positive(atom, fromNegatedConjecture(&stated));
  checkUnitOutput(&positive, "tff", "conjecture", "(~ p)");
  auto negation = new NegatedFormula(atom);
  FormulaUnit negated(negation, fromNegatedConjecture(&stated));
  checkUnitOutput(&negated, "tff", "conjecture", "p");
  FormulaUnit negativeLiteral(new AtomicFormula(Literal::complementaryLiteral(p())),
      fromNegatedConjecture(&stated));
  checkUnitOutput(&negativeLiteral, "tff", "conjecture", "p");

  auto sort = AtomicSort::defaultSort();
  DECL_CONST(a, sort)
  DECL_CONST(b, sort)
  FormulaUnit negativeEquality(new AtomicFormula(Literal::createEquality(false, a, b, sort)),
      fromNegatedConjecture(&stated));
  checkUnitOutput(&negativeEquality, "tff", "conjecture", "a = b");
}

TEST_FUN(unit_stream_closes_free_conjecture_variables_without_changing_input)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort})
  auto atom = new AtomicFormula(p(x));
  FormulaUnit stated(atom, FromInput(UnitInputType::CONJECTURE));
  FormulaUnit conjecture(atom, fromNegatedConjecture(&stated));
  checkUnitOutput(&conjecture, "tff", "conjecture", "(~ (![X0] : (p(X0))))");
  ASS(conjecture.formula() == atom);
  ASS_EQ(Shell::TPTPPrinter::toString(atom), "p(X0)");
}

TEST_FUN(unit_stream_preserves_clause_order_and_conjecture_role)
{
  // Clause: p | q, derived from the negated conjecture.
  // Print cnf(uN,negated_conjecture,( p | q )) or tcf(uN,negated_conjecture,( p | q )).
  // uN is the generated unit name; the ground clause needs no variable prefix.
  DECL_PRED(p, {})
  DECL_PRED(q, {})
  auto clause = Clause::fromLiterals({p(), q()}, FromInput(UnitInputType::CONJECTURE));
  checkUnitOutput(clause, "cnf", "negated_conjecture", "( p | q )");
  checkUnitOutput(clause, "tcf", "negated_conjecture", "( p | q )", true);
}

static std::string printNamedUnit(const char* name, const char* role, Unit* unit,
    bool includeSplitLevels = false)
{
  std::ostringstream out;
  out << Shell::TPTPPrinter::namedUnit(unit, name, role, /*typedClauses=*/true, includeSplitLevels);
  return out.str();
}

TEST_FUN(named_unit_stream_uses_given_name_and_role)
{
  // Clause: p(X0) | q. With name c and role claim, print:
  // tcf(c,claim, ![X0 : $i] : ( p(X0) | q )).
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort})
  DECL_PRED(q, {})
  auto clause = Clause::fromLiterals({p(x), q()}, FromInput(UnitInputType::AXIOM));
  ASS_EQ(printNamedUnit("c", "claim", clause), "tcf(c,claim,\n    ![X0 : $i] : ( p(X0) | q )).\n");

  // Clause: p(X0), under split levels 3 and 4. With split-level output enabled:
  // tcf(s,claim, ![X0 : $i] : ( p(X0) | $splitLevel3 | $splitLevel4 )).
  // With it disabled: tcf(s,claim, ![X0 : $i] : ( p(X0) )).
  auto split = Clause::fromLiterals({p(x)}, FromInput(UnitInputType::AXIOM));
  split->setSplits(SplitSet::getRange(3, 5));
  ASS_EQ(printNamedUnit("s", "claim", split, true),
      "tcf(s,claim,\n    ![X0 : $i] : ( p(X0) | $splitLevel3 | $splitLevel4 )).\n");
  ASS_EQ(printNamedUnit("s", "claim", split), "tcf(s,claim,\n    ![X0 : $i] : ( p(X0) )).\n");

  // The role is the caller's, so a conjecture is not negated back.
  FormulaUnit stated(new AtomicFormula(q()), FromInput(UnitInputType::CONJECTURE));
  FormulaUnit negated(new NegatedFormula(new AtomicFormula(q())), fromNegatedConjecture(&stated));
  ASS_EQ(printNamedUnit("f", "conjecture", &negated), "tff(f,conjecture,\n    (~ q)).\n");
}
