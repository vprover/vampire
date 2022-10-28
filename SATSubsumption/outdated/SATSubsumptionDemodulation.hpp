#if 0
#ifndef SATSUBSUMPTION_HPP
#define SATSUBSUMPTION_HPP

#include "Kernel/Clause.hpp"
#include "Lib/STL.hpp"
#include "Inferences/InferenceEngine.hpp"

namespace SATSubsumption {


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
    bool checkSubsumption(Kernel::Clause* side_premise, Kernel::Clause* main_premise);
    void benchmark_micro(vvector<SubsumptionInstance> instances);
};


}

#endif /* !SATSUBSUMPTION_HPP */

#endif
