/**
 * @file Rule/ProofAttempt.hpp
 * Defines class ProofAttempt implementing a resolution proof attempt.
 * @since 12/07/2008 Linz
 */

#ifndef __Rule_ProofAttempt__
#define __Rule_ProofAttempt__

#include "../Kernel/Unit.hpp"

using namespace Kernel;

namespace Rule {

/**
 * Class ProofAttempt implementing a rule-based proof attempt.
 * @since 12/07/2008 Linz
 */
class ProofAttempt
{
public:
  void prove(UnitList* us);
private:
}; // class ProofAttempt

}

#endif
