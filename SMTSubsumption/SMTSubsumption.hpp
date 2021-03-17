#ifndef SMTSUBSUMPTION_HPP
#define SMTSUBSUMPTION_HPP

#include "Kernel/Clause.hpp"
#include "Lib/STL.hpp"
#include "Inferences/InferenceEngine.hpp"

#include <memory>

namespace SMTSubsumption {


struct SubsumptionInstance
{
  unsigned int number;
  Kernel::Clause* side_premise;  // also called "base clause"
  Kernel::Clause* main_premise;  // also called "instance clause"
  bool subsumed;  // expected result
};

class SMTSubsumptionImpl2;

class SMTSubsumptionImpl3;

class ProofOfConcept {
  public:
    CLASS_NAME(ProofOfConcept);
    USE_ALLOCATOR(ProofOfConcept);

    ProofOfConcept();
    ~ProofOfConcept();

    void test(Kernel::Clause* side_premise, Kernel::Clause* main_premise);
    void benchmark_run(vvector<SubsumptionInstance> instances);
    void benchmark_micro(vvector<SubsumptionInstance> instances);

    bool checkSubsumption(Kernel::Clause* base, Kernel::Clause* instance);

    // TODO: check if subsat-based implementation also discovers 'result' by SR (need to enumerate all, because there may be more than one possible SR inference)
    // For correctness checking, we need to enumerate all possible subsumption resolution consequences.
    // TODO: add an RSTAT_MCTR to see the distribution of "number of possible consequences per SR". (just to see how common this situation is.)
    bool checkSubsumptionResolution(Kernel::Clause* base, Kernel::Clause* instance, Kernel::Clause* result);

  private:
    std::unique_ptr<SMTSubsumptionImpl2> m_subsat_impl;
};


}

#endif /* !SMTSUBSUMPTION_HPP */
