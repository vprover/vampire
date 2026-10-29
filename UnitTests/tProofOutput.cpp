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
  const auto expected = std::string(proofLanguage()) + "(f4_D,definition,(\n"
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
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort})
  DECL_PRED(name, {})
  Literal* namingLiteral = name();
  auto output = printSplittingComponent({p(x), namingLiteral}, namingLiteral);
  ASS(output.find("( ! [X0] : p(X0) ) <=> ~name") != std::string::npos);
}

TEST_FUN(splitting_definition_preserves_order_and_deduplicates_variables)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort})
  DECL_PRED(r, {sort, sort})
  DECL_PRED(name, {sort, sort})
  Literal* namingLiteral = name(x, y);
  auto output = printSplittingComponent({r(x, z), p(y), r(x, z), namingLiteral}, namingLiteral);
  ASS(output.find("( ! [X1,X0] : (( ! [X2] : (r(X0,X2) | p(X1) | r(X0,X2)) ) <=> ~name(X0,X1)) )")
      != std::string::npos);
}

static std::string expectedClause(const Clause* clause, bool typed, const std::string& body)
{
  return std::string(typed ? "tcf" : "cnf") + "(u" + std::to_string(clause->number())
      + ",axiom,\n    " + body + ").\n";
}

TEST_FUN(typed_clause_prefix_sorts_variables_and_spells_out_sorts)
{
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort, sort})
  auto clause = Clause::fromLiterals({p(y, x)}, FromInput(UnitInputType::AXIOM));
  ASS_EQ(Shell::TPTPPrinter::toString(clause, true),
      expectedClause(clause, true, "![X0 : $i,X1 : $i] : ( p(X1,X0) )"));
  ASS_EQ(Shell::TPTPPrinter::toString(clause, false),
      expectedClause(clause, false, "( p(X1,X0) )"));

  DECL_PRED(q, {AtomicSort::intSort(), sort})
  auto mixed = Clause::fromLiterals({q(y, x)}, FromInput(UnitInputType::AXIOM));
  ASS_EQ(Shell::TPTPPrinter::toString(mixed, true),
      expectedClause(mixed, true, "![X0 : $i,X1 : $int] : ( q(X1,X0) )"));
}

TEST_FUN(typed_clause_prefix_omits_ground_and_empty_quantifiers)
{
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
  PredSugar p("p", {SortSugar(TermList::var(101))}, 1);
  SortSugar type(TermList::var(3));
  TermSugar term(TermList::var(0), type);
  auto clause = Clause::fromLiterals({p(type, term)}, FromInput(UnitInputType::AXIOM));
  ASS_EQ(Shell::TPTPPrinter::toString(clause, true),
      expectedClause(clause, true, "![X3 : $tType,X0 : X3] : ( p(X3,X0) )"));
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
  auto sort = AtomicSort::defaultSort();
  DECL_DEFAULT_VARS
  DECL_PRED(p, {sort})
  DECL_PRED(q, {})
  auto clause = Clause::fromLiterals({p(x), q()}, FromInput(UnitInputType::AXIOM));
  ASS_EQ(printNamedUnit("c", "claim", clause), "tcf(c,claim,\n    ![X0 : $i] : ( p(X0) | q )).\n");

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
