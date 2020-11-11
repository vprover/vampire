#ifndef SMTSUBSUMPTION_HPP
#define SMTSUBSUMPTION_HPP

#include "Kernel/Clause.hpp"
#include "Lib/STL.hpp"
#include "Inferences/InferenceEngine.hpp"

namespace SMTSubsumption {


struct SubsumptionInstance
{
  unsigned int number;
  Kernel::Clause* side_premise;  // also called "base clause"
  Kernel::Clause* main_premise;  // also called "instance clause"
  bool subsumed;  // expected result
};


class ProofOfConcept {
  public:
    CLASS_NAME(ProofOfConcept);
    USE_ALLOCATOR(ProofOfConcept);

    void test(Kernel::Clause* side_premise, Kernel::Clause* main_premise);
    bool checkSubsumption(Kernel::Clause* side_premise, Kernel::Clause* main_premise, bool debug_messages = false);

    void benchmark_micro(vvector<SubsumptionInstance> instances);
    void benchmark_micro1(SubsumptionInstance instance);
};


}

#endif /* !SMTSUBSUMPTION_HPP */
