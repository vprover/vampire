#ifndef SMTSUBSUMPTION_HPP
#define SMTSUBSUMPTION_HPP

#include "Kernel/Clause.hpp"
#include "Inferences/InferenceEngine.hpp"


class SMTSubsumption {
  public:
    CLASS_NAME(SMTSubsumption);
    USE_ALLOCATOR(SMTSubsumption);

    void test(Kernel::Clause* side_premise, Kernel::Clause* main_premise);
};



#endif /* !SMTSUBSUMPTION_HPP */
