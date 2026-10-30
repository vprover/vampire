/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file TPTPProofPrinter.cpp
 * Implements TPTPOutput and InferenceStore::TPTPProofPrinter.
 */

#include <functional>

#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Set.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/Stack.hpp"
#include "Lib/StringUtils.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "Parse/TPTP.hpp"
#include "SAT/SATInference.hpp"
#include "Saturation/Splitter.hpp"
#include "Shell/UIHelper.hpp"

#include "TPTPProofPrinter.hpp"

#include "Forwards.hpp"

namespace Shell {

using namespace std;

namespace TPTPOutput {

Language proofLanguage()
{
  // Use the unpreprocessed input: preprocessing can remove sorts and higher
  // order features, but the proof must not claim a stronger fragment than it.
  if (env.initiallyHigherOrder()) { return Language::THF; }
  if (env.initiallyHasNonDefaultSorts()) { return Language::TFF; }
  return Language::FOF;
}

} // namespace TPTPOutput

} // namespace Shell

namespace Kernel {

using namespace std;
using namespace Lib;
using namespace Shell;
using namespace SAT;

namespace {

// A copyable view of the native premise iterator, without building a UnitList.
struct PremiseIterator {
  using ElementType = Unit*;
  const Inference* inference;
  Inference::Iterator position;

  bool hasNext() { return inference->hasNext(position); }
  Unit* next() { return inference->next(position); }
};

auto parentUnits(const Unit* unit)
{
  const auto& inference = unit->inference();
  return iterTraits(PremiseIterator{&inference, inference.iterator()});
}

} // namespace

using namespace Shell::TPTPOutput;
// std and SAT, used above, have names of their own for these.
using Shell::TPTPOutput::disjunction;
namespace Status = Shell::TPTPOutput::Status;

InferenceStore::TPTPProofPrinter::TPTPProofPrinter(std::ostream& out, InferenceStore* is)
  : AbstractSATProofPrinter(out, is)
{}

void InferenceStore::TPTPProofPrinter::print()
{
    //an fof proof needs no type declarations, and the signature can hold a
    //typed symbol no unit ever used, whose declaration would put a tff line
    //into an otherwise fof proof
    if(env.initiallyHasNonDefaultSorts() || env.initiallyHigherOrder()){
      //outputSymbolDeclarations also deals with sorts for now
      //UIHelper::outputSortDeclarations(out);
      UIHelper::outputSymbolDeclarations(out);
    }
    AbstractSATProofPrinter::print();
  }

const char* InferenceStore::TPTPProofPrinter::getRole(InferenceRule rule, UnitInputType origin)
{
    if (isTheoryAxiomRule(rule)) {
      return Role::AXIOM;
    }
    switch(rule) {
    case InferenceRule::INPUT:
      // Proofs present hypotheses and extensionality axioms as axioms.
      if (origin == UnitInputType::ASSUMPTION || origin == UnitInputType::EXTENSIONALITY_AXIOM) {
        return Role::AXIOM;
      }
      return inputRole(origin);
    case InferenceRule::NEGATED_CONJECTURE:
      return Role::NEGATED_CONJECTURE;
    case InferenceRule::AVATAR_DEFINITION:
    case InferenceRule::FUNCTION_DEFINITION:
    case InferenceRule::PREDICATE_DEFINITION:
    case InferenceRule::FOOL_ITE_DEFINITION:
    case InferenceRule::FOOL_LET_DEFINITION:
    case InferenceRule::FOOL_FORMULA_DEFINITION:
    case InferenceRule::FOOL_MATCH_DEFINITION:
    case InferenceRule::GENERAL_SPLITTING_COMPONENT:
    case InferenceRule::INEQUALITY_SPLITTING_NAME_INTRODUCTION:
    case InferenceRule::EQUALITY_PROXY_DEFINITION:
      return Role::DEFINITION;
    case InferenceRule::THEORY_TAUTOLOGY_SAT_CONFLICT:
    case InferenceRule::HILBERTS_CHOICE_INSTANCE:
    case InferenceRule::DISTINCTNESS_AXIOM:
      return Role::AXIOM;
    default:
      return Role::PLAIN;
    }
  }

std::string InferenceStore::TPTPProofPrinter::tptpRuleName(InferenceRule rule)
{
    return StringUtils::replaceChars<' ', '-'>(ruleName(rule), '_');
}

std::ostream& InferenceStore::TPTPProofPrinter::printSplits(std::ostream& out, SplitSet* values)
{
  ASS_G(values->size(), 0);
  auto splitLiterals = disjunction(iterTraits(values->iter()).map([](SplitLevel split) {
    return Saturation::Splitter::getLiteralFromName(split).opposite();
  }));
  if (values->size() > 1) {
    return out << parenthesized(std::move(splitLiterals));
  }
  return out << splitLiterals;
}

std::ostream& InferenceStore::TPTPProofPrinter::printFormula(std::ostream& out, Unit* unit)
{
  out << universalClosure(unit, proofLanguage());
  if (unit->isClause()) {
    SplitSet* clauseSplits = unit->asClause()->splits();
    if (clauseSplits && !clauseSplits->isEmpty()) {
      out << connectiveSymbol(OR) << splits(clauseSplits);
    }
  }
  return out;
}

bool InferenceStore::TPTPProofPrinter::hasNewSymbols(Unit* u)
{
    bool res = _is->_introducedSymbols.find(u->number());
    ASS(!res || _is->_introducedSymbols.get(u->number()).isNonEmpty());
    if(!res){
      res = _is->_introducedSplitNames.find(u->number());
    }
    return res;
  }

std::ostream& InferenceStore::TPTPProofPrinter::printNewSymbols(std::ostream& out, const char* origin, Unit* unit)
{
  ASS(hasNewSymbols(unit));
  if (_is->_introducedSplitNames.find(unit->number())) {
    return out << newSymbolAnnotation(origin, _is->_introducedSplitNames.get(unit->number()));
  }
  const auto& symbols = _is->_introducedSymbols.get(unit->number());
  return out << newSymbolAnnotation(origin,
      commaSeparated(SymbolStack::ConstIterator(symbols), std::mem_fn(&Signature::Symbol::name)));
}

std::ostream& InferenceStore::TPTPProofPrinter::printSkolemizeMap(std::ostream& out, Unit* unit)
{
  ASS(hasNewSymbols(unit));
  const auto& symbols = _is->_introducedSymbols.get(unit->number());
  return out << commaSeparated(SymbolStack::ConstIterator(symbols),
      [this](const Signature::Symbol* symbol) { return skolemizeSymbol(symbol); });
}

std::ostream& InferenceStore::TPTPProofPrinter::printSkolemizeSymbol(std::ostream& out, const Signature::Symbol* symbol)
{
  auto skolemTerm = _is->_introducedSkolemSymTerms.find(symbol);
  NEVER(skolemTerm.isNone());
  auto skolemizedVariable = _is->_introducedSymbolReplacedVars.find(symbol);
  NEVER(skolemizedVariable.isNone());

  out << "skolemize(" << variableRef(*skolemizedVariable) << ',';
  // For now we have to output standard prolog, i.e. f(X1,...,Xn) even in THF.
  // TODO: change this once GDV is updated.
  if (env.higherOrder()) {
    ASS(!TermList(*skolemTerm).isLambdaTerm());
    auto [head, args] = HOL::getHeadAndArgs(TermList(*skolemTerm));
    ASS(head.isTerm() && !head.isLambdaTerm());

    auto h = head.term();
    if (h->isLiteral()) {
      out << static_cast<Literal*>(h)->predicateName();
    } else if (h->isSort()) {
      out << static_cast<AtomicSort*>(h)->typeConName();
    } else {
      out << h->functionName();
    }

    if (h->arity() || args.size()) {
      auto variables = concatIters(
          range(0, h->arity()).map([h](unsigned i) { return *h->nthArgument(i); }),
          arrayIter(args));
      out << parenthesized(commaSeparated(variables.map([](TermList variable) {
        ASS(variable.isVar());
        return variable;
      })));
    }
  } else {
    out << **skolemTerm;
  }
  return out << ')';
}

void InferenceStore::TPTPProofPrinter::printStep(Unit* unit)
{
  InferenceRule rule = unit->inference().rule();
  switch (rule) {
  case InferenceRule::GENERAL_SPLITTING_COMPONENT:
    printGeneralSplittingComponent(out, unit);
    return;
  case InferenceRule::GENERAL_SPLITTING:
    printSplitting(out, unit);
    return;
  default: ;
  }

  out << proofStep(unitRef(unit), getRole(rule, unit->inputType()), formula(unit), inference(unit));
}

std::ostream& InferenceStore::TPTPProofPrinter::printInference(std::ostream& out, Unit* unit)
{
  InferenceRule rule = unit->inference().rule();
  if (rule == InferenceRule::INPUT) {
    std::string axiomName;
    std::filesystem::path axiomPath;
    if (!Parse::TPTP::findAxiomName(unit, axiomName, axiomPath)) {
      // Giles' ucore extraction code parses labels from smtlib files, let's try printing these too.
      axiomName = !unit->isClause() && unit->getFormula()->hasLabel()
          ? unit->getFormula()->getLabel() : UNKNOWN_SOURCE;
      axiomPath = UNKNOWN_SOURCE;
    }
    return out << "file('" << axiomPath.string() << "','" << axiomName << "')";
  }

  if (!parentUnits(unit).hasNext()) {
    if (hasNewSymbols(unit)) {
      return out << introducedAnnotation(Origin::DEFINITION, newSymbols(Origin::DEFINITION, unit), tptpRuleName(rule));
    }
    // Without introduced symbols we have to claim that the axiom comes from a theory.
    return out << introducedAnnotation(Origin::THEORY, tptpRuleName(rule), Output::Nothing{});
  }
  return out << inferenceAnnotation(tptpRuleName(rule), status(unit), premises(unit));
}

std::ostream& InferenceStore::TPTPProofPrinter::printStatus(std::ostream& out, Unit* unit)
{
  switch (unit->inference().rule()) {
  case InferenceRule::SKOLEMIZE:
    return out << statusAnnotation(Status::ESA) << ',' << newSymbols(Origin::SKOLEM, unit) << ','
        << skolemizeMap(unit);
  case InferenceRule::NEGATED_CONJECTURE:
    return out << statusAnnotation(Status::CTH);
  default:
    return out;
  }
}

std::ostream& InferenceStore::TPTPProofPrinter::printPremises(std::ostream& out, Unit* unit)
{
  InferenceRule rule = unit->inference().rule();
  if (rule == InferenceRule::AVATAR_REFUTATION) {
    SATClause* premise = unit->inference().satPremise();
    ASS(premise)
    return out << satRef(premise);
  }

  auto parents = parentUnits(unit);
  if (rule == InferenceRule::GENERAL_SPLITTING) {
    // GeneralSplitting::apply puts the base premise first, followed by components.
    ALWAYS(parents.hasNext());
    out << unitRef(parents.next()) << ',';
    ASS(parents.hasNext()); // We always split off at least one component.
    return out << commaSeparated(parents.map([this](Unit* component) {
      ASS(_is->_splittingNameLiterals.find(component->number()));
      return definitionRef(component);
    }));
  }
  return out << commaSeparated(parents.map(unitRef));
}

void InferenceStore::TPTPProofPrinter::printSATStep(SATClause* clause)
{
  // SAT proof steps retain their compact CNF layout.
  out << Language::CNF << '(' << satRef(clause) << ", " << Role::PLAIN << ", "
      << parenthesized(disjunction(clause->iter())) << ", ";

  auto inference = clause->inference();
  switch (inference->getType()) {
  case SATInference::PROP_INF: {
    auto parents = static_cast<PropInference*>(inference)->getPremises();
    out << inferenceAnnotation(SatRule::RAT, Output::Nothing{},
        commaSeparated(parents->iter(), satRef));
    break;
  }
  case SATInference::FO_CONVERSION:
    out << inferenceAnnotation(SatRule::SAT_CONVERSION, Output::Nothing{},
        unitRef(static_cast<FOConversionInference*>(inference)->getOrigin()));
    break;
  }
  out << ").\n";
}

std::ostream& InferenceStore::TPTPProofPrinter::printSplitting(std::ostream& out, Unit* unit)
{
  ASS(unit->isClause());
  InferenceRule rule = unit->inference().rule();
  ASS(rule == InferenceRule::GENERAL_SPLITTING);
  return out << proofStep(unitRef(unit), getRole(rule, UnitInputType::AXIOM), formula(unit),
      inferenceAnnotation(tptpRuleName(rule), Output::Nothing{}, premises(unit)));
}

std::ostream& InferenceStore::TPTPProofPrinter::printGeneralSplittingComponent(std::ostream& out, Unit* unit)
{
  ASS(unit->isClause());
  ASS(!parentUnits(unit).hasNext());

  // The naming literal must always be recorded for a splitting component.
  Literal* nameLiteral = _is->_splittingNameLiterals.get(unit->number());
  auto nameSymbol = env.signature->getPredicate(nameLiteral->functor());
  InferenceRule rule = unit->inference().rule();

  out << proofStep(unitRef(unit), getRole(InferenceRule::CLAUSIFY, UnitInputType::AXIOM), formula(unit),
      inferenceAnnotation(tptpRuleName(InferenceRule::CLAUSIFY), Output::Nothing{}, definitionRef(unit)));
  return out << proofStep(definitionRef(unit), getRole(rule, UnitInputType::AXIOM),
      splittingDefinition(unit->asClause(), nameLiteral),
      introducedAnnotation(Origin::DEFINITION, newSymbolAnnotation(Origin::DEFINITION, nameSymbol->name()),
          tptpRuleName(rule)));
}

std::ostream& InferenceStore::TPTPProofPrinter::printSplittingDefinition(
    std::ostream& out, Clause* component, Literal* nameLiteral)
{
  DHMap<unsigned, TermList, FnvHash, IdentityHash> sorts;
  SortHelper::collectVariableSorts(component, sorts);

  Stack<unsigned> nameVariables, componentVariables;
  DHSet<unsigned, FnvHash, IdentityHash> seen;
  VariableIterator names(nameLiteral);
  while (names.hasNext()) {
    unsigned variable = names.next().var();
    ASS(!seen.contains(variable)); // Naming arguments are distinct variables.
    seen.insert(variable);
    nameVariables.push(variable);
  }

  Stack<Literal*> literals;
  for (Literal* literal : component->iterLits()) {
    if (literal == nameLiteral) { continue; }
    literals.push(literal);
    VariableIterator variables(literal);
    while (variables.hasNext()) {
      unsigned variable = variables.next().var();
      if (seen.insert(variable)) { componentVariables.push(variable); }
    }
  }
  ASS(literals.isNonEmpty());

  // Literal order and the separate scopes of local and naming variables are preserved.
  auto quantifiedComponent = quantified(QuantifiedVariables(pvi(componentVariables.iterCloned()), sorts, proofLanguage()),
      disjunction(literals.iterFifo()), literals.size() > 1);
  auto definition = Output::deferred([&](std::ostream& out) -> std::ostream& {
    return out << quantifiedComponent << connectiveSymbol(IFF) << *Literal::complementaryLiteral(nameLiteral);
  });
  return out << quantified(QuantifiedVariables(pvi(nameVariables.iterCloned()), sorts, proofLanguage()), definition);
}

} // namespace Kernel
