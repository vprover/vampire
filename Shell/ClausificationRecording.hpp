/*
 * This file is part of Vampire, distributed under the licence found at
 * https://vprover.github.io/license.html and in the source directory.
 */
#ifndef __Shell_ClausificationRecording__
#define __Shell_ClausificationRecording__

#include "Forwards.hpp"
#include "Lib/ProofExtra.hpp"

#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace Shell {

struct NewCNFRecording {
  std::vector<std::string> events;
  std::vector<std::pair<std::string, std::string>> symbols; // kind, name
  std::vector<std::string> skolems;
};

/** Captured before selection changes literal order. Occurrences follow the
 * printed parent, including duplicates and printed equality orientations. */
struct ClausificationExtra : Lib::InferenceExtra {
  struct Occurrence {
    Kernel::Literal* instantiated;
    bool flipped;
  };
  std::vector<std::pair<unsigned, unsigned>> binders;
  std::vector<Occurrence> occurrences;
  /** NewCNF creation choices shared by all clauses from one input unit.
   * Null for old CNF. Cached Skolems occur only once, in creation order. */
  std::shared_ptr<NewCNFRecording> newcnf;
  unsigned clauseIndex = 0;
  void output(std::ostream& out) const override { out << "clausification_certificate"; }
};

struct FOOLExtra : Lib::InferenceExtra {
  std::vector<std::string> rewrites;
  std::string definition;
  void output(std::ostream& out) const override { out << "fool_certificate"; }
};

std::string replayFormula(Kernel::Formula* formula);
std::string replayFOOLTerm(Kernel::TermList term);

/** Capture only a universal prefix followed by a clause-shaped body. Old CNF
 * preserves literal identities and variable names, so no matching or replay
 * is needed. Unsupported formulas and vacuous binders get no certificate. */
void recordClausification(Kernel::FormulaUnit* parent, Kernel::Clause* conclusion);

} // namespace Shell
#endif
