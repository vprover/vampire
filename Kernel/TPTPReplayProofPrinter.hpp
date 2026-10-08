/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable copyright laws.
 * It is distributed under the licence found at https://vprover.github.io/license.html
 */
#ifndef __TPTPReplayProofPrinter__
#define __TPTPReplayProofPrinter__

#include "TPTPProofPrinter.hpp"

#include <memory>

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

private:
  std::unique_ptr<Shell::InferenceReplayer> _replayer;
  bool _replay;
};

} // namespace Kernel

namespace Kernel {
std::string formatTPTPReplayAnnotations(
    Unit* conclusion, const Shell::InferenceRecorder::InferenceReplayAnnotation& replay);
std::string tptpRectificationReplayAnnotation(Unit* conclusion, bool replay);
std::string tptpClausificationReplayAnnotation(Unit* conclusion, bool replay);
std::string tptpAvatarSplitInstantiationReplayAnnotation(Unit* conclusion);
std::string tptpAvatarConversionReplayAnnotation(Unit* origin);
std::vector<Unit*> tptpAvatarConversionReplayDefinitions(Unit* origin);
}

#endif
