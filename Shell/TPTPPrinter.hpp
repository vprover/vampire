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
 * @file TPTPPrinter.hpp
 * Defines class TPTPPrinter and InferenceStore::TPTPProofPrinter.
 */

#ifndef __TPTPPrinter__
#define __TPTPPrinter__

#include <iosfwd>

#include "Kernel/InferenceStore.hpp"
#include "Forwards.hpp"



namespace Shell {

using namespace Kernel;

/**
 * All purpose TPTP printer class. It has two major roles:
 * 1. returns as a TPTP string a Unit/Formula
 * 2. it outputs to the desired output stream any Unit specified
 */
class TPTPPrinter {
public:
  TPTPPrinter(std::ostream* tgtStream=0);

  void print(Unit* u);
  void printAsClaim(std::string name, Unit* u);
  void printWithRole(std::string name, std::string role, Unit* u, bool includeSplitLevels = true);

  /** With @b typedClauses, a clause is printed as a tcf() unit, i.e. with an
   *  explicit universal prefix spelling out the sort of each of its variables;
   *  without it, as a cnf() unit. Formulas are printed as tff() either way. */
  static std::string toString(const Unit*, bool typedClauses = false);
  static std::string toString(const Formula*);
  static std::string toString(const Term*);
  static std::string toString(const Literal*);

private:

  std::string getBodyStr(Unit* u, bool includeSplitLevels);

  static std::string universalPrefix(const Unit* unit);

  void ensureHeadersPrinted(Unit* u);
  void outputSymbolTypeDefinitions(unsigned symNumber, SymbolType symType);

  void ensureNecesarySorts();
  void printTffWrapper(Unit* u, std::string bodyStr);

  std::ostream& tgt();

  /** if zero, we print to std::cout */
  std::ostream* _tgtStream;

  bool _headersPrinted;
};

}

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

#endif // __TPTPPrinter__
