#ifndef SMTSUBSUMPTION_HPP
#define SMTSUBSUMPTION_HPP

#include "Kernel/Clause.hpp"
#include "Lib/STL.hpp"
#include "Inferences/InferenceEngine.hpp"

#include <memory>

namespace SMTSubsumption {


struct SubsumptionInstance
{
  Kernel::Clause* side_premise;  ///< also called "base clause"
  Kernel::Clause* main_premise;  ///< also called "instance clause"
  unsigned int number;
  int subsumed;  // expected result
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
    bool checkSubsumptionResolution(Kernel::Clause* base, Kernel::Clause* instance, Kernel::Clause* conclusion);

    void setupMainPremise(Kernel::Clause* instance);
    bool setupSubsumption(Kernel::Clause* base);
    bool solve();

  private:
    void add_common_benchmark_args(vvector<vstring>& args);
    void init_benchmark(vvector<vstring> the_args);

  private:
    std::unique_ptr<SMTSubsumptionImpl2> m_subsat_impl;
    std::unique_ptr<SMTSubsumptionImpl3> m_subsat_impl3;
};


}

#endif /* !SMTSUBSUMPTION_HPP */
