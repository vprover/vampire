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

class ProofOfConcept {
  public:
    CLASS_NAME(ProofOfConcept);
    USE_ALLOCATOR(ProofOfConcept);

    ProofOfConcept();
    ~ProofOfConcept();

    void test(Kernel::Clause* side_premise, Kernel::Clause* main_premise);
    void benchmark_micro(vvector<SubsumptionInstance> instances);

    bool checkSubsumption(Kernel::Clause* base, Kernel::Clause* instance);

  private:
    std::unique_ptr<SMTSubsumptionImpl2> m_subsat_impl;
};


}

#endif /* !SMTSUBSUMPTION_HPP */
