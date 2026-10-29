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
 * @file TPTPProofPrinter.hpp
 * Defines InferenceStore::TPTPProofPrinter and the parts of TPTPOutput specific to
 * TPTP derivations, which it shares with the proof-check printer.
 */

#ifndef __TPTPProofPrinter__
#define __TPTPProofPrinter__

#include <iosfwd>
#include <string_view>
#include <tuple>

#include "Lib/Metaiterators.hpp"
#include "Lib/Option.hpp"
#include "Lib/Output.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/InferenceStore.hpp"
#include "SAT/SATLiteral.hpp"
#include "SAT/SATClause.hpp"
#include "Shell/TPTPConstants.hpp"
#include "Shell/TPTPPrinter.hpp"
#include "Forwards.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

/** Formatting shared by the TPTP proof and proof-check printers. */
namespace TPTPOutput {

/** Language of the unpreprocessed input, preserved throughout the proof. */
const char* proofLanguage();



/* Printable building blocks of TPTP proof steps, for the proof printers. */

inline Reference unitRef(const Unit* unit) { return {"f", unit->number()}; }
inline Reference satRef(const SAT::SATClause* clause) { return {"s", clause->number}; }
inline Reference definitionRef(const Unit* unit) { return {"f", unit->number(), "_D"}; }

/** A TPTP annotation term <type>(<argument>,...,<argument>), with at least one argument. */
template<Output::Printable First, Output::Printable... Rest>
struct Annotation {
  const char* type;
  std::tuple<First, Rest...> arguments;

  friend std::ostream& operator<<(std::ostream& out, Annotation const& self)
  {
    out << self.type << '(';
    std::apply([&](First const& first, Rest const&... rest) {
      out << first;
      ((out << ',' << rest), ...);
    }, self.arguments);
    return out << ')';
  }
};

/* The list arguments of the factories below are printable list contents, without the brackets. */

template<Output::Printable Rule, Output::Printable Annotations, Output::Printable Premises>
Annotation<Rule, Bracketed<Annotations>, Bracketed<Premises>>
inferenceAnnotation(Rule rule, Annotations annotations, Premises premises)
{
  return {AnnotationType::INFERENCE,
      std::tuple(std::move(rule), bracketed(std::move(annotations)), bracketed(std::move(premises)))};
}

template<Output::Printable Annotations, Output::Printable Details>
Annotation<const char*, Bracketed<Annotations>, Bracketed<Details>>
introducedAnnotation(const char* origin, Annotations annotations, Details details)
{
  return {AnnotationType::INTRODUCED,
      std::tuple(origin, bracketed(std::move(annotations)), bracketed(std::move(details)))};
}

template<Output::Printable Symbols>
Annotation<const char*, Bracketed<Symbols>> newSymbolAnnotation(const char* origin, Symbols symbols)
{ return {AnnotationType::NEW_SYMBOLS, std::tuple(origin, bracketed(std::move(symbols)))}; }

/** status(<status>), with a status from Status. */
inline Annotation<const char*> statusAnnotation(const char* status)
{ return {AnnotationType::STATUS, std::tuple(status)}; }

/** Complete FOF/TFF/THF proof step, including layout, terminator, and flush. */
template<Output::Printable Body, Output::Printable Source>
struct ProofStep {
  Reference reference;
  const char* role;
  Body body;
  Source source;

  friend std::ostream& operator<<(std::ostream& out, ProofStep const& self)
  {
    return out << proofLanguage() << '(' << self.reference << ',' << self.role << ",(\n  "
        << self.body << "),\n  " << self.source << ")." << std::endl;
  }
};

template<Output::Printable Body, Output::Printable Source>
ProofStep<Body, Source> proofStep(Reference reference, const char* role, Body body, Source source)
{ return {reference, role, std::move(body), std::move(source)}; }

} // namespace TPTPOutput
} // namespace Shell

namespace Kernel {

struct InferenceStore::TPTPProofPrinter : InferenceStore::AbstractSATProofPrinter
{
  TPTPProofPrinter(std::ostream& out, InferenceStore* is);
  void print() override;

protected:
  void printStep(Unit* unit) override;
  void printSATStep(SAT::SATClause* clause) override;
  const char* getRole(InferenceRule rule, UnitInputType origin);
  std::string tptpRuleName(InferenceRule rule);

  /* Printable views of the print... members below.
   *
   * This lets the views be passed as arguments to the TPTPOutput annotations
   * (proofStep, inferenceAnnotation, ...) and nested inside each other. */
  template<auto Write, class... Args>
    requires Output::MemberWriter<Write, TPTPProofPrinter, std::decay_t<Args>...>
  auto fragment(Args&&... args) {
    return Output::deferredMember<Write>(this, std::forward<Args>(args)...);
  }
  auto splits(SplitSet* value) {
    return fragment<&TPTPProofPrinter::printSplits>(value);
  }
  auto formula(Unit* unit) {
    return fragment<&TPTPProofPrinter::printFormula>(unit);
  }
  auto inference(Unit* unit) {
    return fragment<&TPTPProofPrinter::printInference>(unit);
  }
  auto status(Unit* unit) {
    return fragment<&TPTPProofPrinter::printStatus>(unit);
  }
  auto premises(Unit* unit) {
    return fragment<&TPTPProofPrinter::printPremises>(unit);
  }
  auto newSymbols(const char* origin, Unit* unit) {
    return fragment<&TPTPProofPrinter::printNewSymbols>(origin, unit);
  }
  auto skolemizeMap(Unit* unit) {
    return fragment<&TPTPProofPrinter::printSkolemizeMap>(unit);
  }
  auto skolemizeSymbol(const Signature::Symbol* symbol) {
    return fragment<&TPTPProofPrinter::printSkolemizeSymbol>(symbol);
  }
  auto splittingDefinition(Clause* component, Literal* nameLiteral) {
    return fragment<&TPTPProofPrinter::printSplittingDefinition>(component, nameLiteral);
  }

  std::ostream& printSplits(std::ostream& out, SplitSet* splits);
  std::ostream& printFormula(std::ostream& out, Unit* unit);
  std::ostream& printInference(std::ostream& out, Unit* unit);
  std::ostream& printStatus(std::ostream& out, Unit* unit);
  std::ostream& printPremises(std::ostream& out, Unit* unit);
  bool hasNewSymbols(Unit* unit);
  std::ostream& printNewSymbols(std::ostream& out, const char* origin, Unit* unit);
  std::ostream& printSkolemizeMap(std::ostream& out, Unit* unit);
  std::ostream& printSkolemizeSymbol(std::ostream& out, const Signature::Symbol* symbol);
  std::ostream& printSplittingDefinition(std::ostream& out, Clause* component, Literal* nameLiteral);
  std::ostream& printSplitting(std::ostream& out, Unit* unit);
  std::ostream& printGeneralSplittingComponent(std::ostream& out, Unit* unit);
};

} // namespace Kernel

#endif // __TPTPProofPrinter__

