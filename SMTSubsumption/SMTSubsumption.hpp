#ifndef SMTSUBSUMPTION_HPP
#define SMTSUBSUMPTION_HPP

#include "Kernel/Clause.hpp"
#include "Inferences/InferenceEngine.hpp"

namespace SMTSubsumption {


class ProofOfConcept {
  public:
    CLASS_NAME(ProofOfConcept);
    USE_ALLOCATOR(ProofOfConcept);

    void test(Kernel::Clause* side_premise, Kernel::Clause* main_premise);
    bool checkSubsumption(Kernel::Clause* side_premise, Kernel::Clause* main_premise, bool debug_messages = false);
};


}

#endif /* !SMTSUBSUMPTION_HPP */
