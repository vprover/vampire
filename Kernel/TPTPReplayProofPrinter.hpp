/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable copyright laws.
 * It is distributed under the licence found at https://vprover.github.io/license.html
 */
#ifndef __TPTPReplayProofPrinter__
#define __TPTPReplayProofPrinter__

#include "TPTPProofPrinter.hpp"

#include <memory>
#include <set>

namespace Shell { class InferenceReplayer; }

namespace Kernel {

struct InferenceStore::TPTPReplayProofPrinter : InferenceStore::TPTPProofPrinter
{
  TPTPReplayProofPrinter(std::ostream& out, InferenceStore* is);
  ~TPTPReplayProofPrinter() override;

protected:
  void appendInferenceReplayAnnotations(Unit* unit, std::string& status,
      Shell::InferenceRecorder::InferenceReplayAnnotation& replay) override;
  std::string avatarConversionReplayAnnotation(Unit* origin) const override;
  std::vector<Unit*> avatarConversionReplayDefinitions(Unit* origin) const override;
  void addAdditionalPremises(Unit* unit, std::vector<Unit*>& todo) override;
  std::string parentlessReplayAnnotation(Unit* unit,
      Shell::InferenceRecorder::InferenceReplayAnnotation& replay) override;

private:
  std::string higherOrderReplayAnnotation(
      const Shell::InferenceRecorder::InferenceInformation* information);

  std::unique_ptr<Shell::InferenceReplayer> _replayer;
  bool _replay;
  /** Vampire-introduced symbols whose introduction was already printed. */
  std::set<unsigned> _introducedSymbols;
  std::set<std::string> _introducedCNFSymbols;
};

} // namespace Kernel

namespace Kernel {
std::string formatTPTPReplayAnnotations(
    Unit* conclusion, const Shell::InferenceRecorder::InferenceReplayAnnotation& replay);
std::string tptpReplayTerm(TermList term);
std::string tptpDefinitionUnfoldingReplayAnnotation(Unit* conclusion);
/** Replace only the zero-based `occurrence`-th subterm of `literal` equal to
 * `from`, in the order documented for `occurrence(n)` certificates: arguments
 * left to right, a node before its arguments, and no descent into a match.
 * Sorts are never visited. Return nullptr if there are fewer occurrences. */
Literal* replaceOccurrence(Literal* literal, TermList from, TermList to, unsigned occurrence);
std::string tptpRectificationReplayAnnotation(Unit* conclusion, bool replay);
std::string tptpClausificationReplayAnnotation(Unit* conclusion, bool replay);
std::string tptpAvatarSplitInstantiationReplayAnnotation(Unit* conclusion);
std::string tptpAvatarConversionReplayAnnotation(Unit* origin);
std::vector<Unit*> tptpAvatarConversionReplayDefinitions(Unit* origin);
}

#endif
