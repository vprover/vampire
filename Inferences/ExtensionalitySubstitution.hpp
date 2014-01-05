/**
 * @file ExtensionalitySubstitution.hpp
 * Defines class ExtensionalitySubstitution
 *
 */

#ifndef __ExtensionalitySubstitution__
#define __ExtensionalitySubstitution__

#include "Forwards.hpp"

#include "Saturation/ExtensionalityClauseContainer.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;

class ExtensionalitySubstitution
: public GeneratingInferenceEngine
{
public:
  ExtensionalitySubstitution() {}
  
  ClauseIterator generateClauses(Clause* premise);

  static Clause* performExtensionalitySubstitution(
    Clause* extCl, Literal* extLit,
    Clause* otherCl, Literal* otherLit,
    RobSubstitution* subst);
private:
  struct ForwardPairingFn;
  struct ForwardUnificationsFn;
  struct ForwardResultFn;

  struct NegEqSortFn;
  struct BackwardPairingFn;
  struct BackwardUnificationsFn;
  struct BackwardResultFn;

  ExtensionalityClauseContainer* _extClauses;
};

};

#endif /*__ExtensionalitySubstitution__*/
