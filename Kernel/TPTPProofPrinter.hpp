/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable copyright laws.
 * It is distributed under the licence found at https://vprover.github.io/license.html
 */
#ifndef __Kernel_TPTPProofPrinter__
#define __Kernel_TPTPProofPrinter__

#include "InferenceStore.hpp"

#include <string>
#include <vector>

namespace Kernel {

using namespace Lib;

/** Quantify a proof body over unique variables, preserving their iteration order. */
std::string getQuantifiedStr(VirtualIterator<unsigned> variables, std::string inner,
    DHMap<unsigned, TermList, FnvHash, IdentityHash>& sorts, bool innerParentheses = true);

/** Return the universally closed unit, excluding the supplied variables. */
std::string getQuantifiedStr(Unit* unit, List<unsigned>* nonQuantified = nullptr);

struct InferenceStore::TPTPProofPrinter : InferenceStore::AbstractSATProofPrinter
{
  TPTPProofPrinter(std::ostream& out, InferenceStore* is);
  void print() override;

protected:
  void printStep(Unit* unit) override;
  void printSATStep(SAT::SATClause* clause) override;
  std::string getRole(InferenceRule rule, UnitInputType origin);
  std::string tptpRuleName(InferenceRule rule);
  std::string unitIdToTptp(std::string unitId);
  std::string tptpUnitId(Unit* unit);
  std::string tptpDefId(Unit* unit);
  std::string splitsToString(SplitSet* splits);
  std::string getFofString(std::string id, std::string formula, std::string inference,
                           InferenceRule rule, UnitInputType origin = UnitInputType::AXIOM);
  std::string getFormulaString(Unit* unit);
  bool hasNewSymbols(Unit* unit);
  std::string getNewSymbols(std::string origin, std::string symbols);
  std::string getNewSymbols(std::string origin, SymbolStack::ConstIterator symbols);
  std::string getNewSymbols(std::string origin, Unit* unit);
  std::string getSkolemizeMap(Unit* unit);
  std::string getSkolemizeMap(SymbolStack::ConstIterator symbols);
  void printSplitting(Unit* unit);
  void printGeneralSplittingComponent(Unit* unit);

  std::string splitPrefix;
};

} // namespace Kernel

#endif
