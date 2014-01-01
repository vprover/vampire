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

private:
  struct MatchingSortFn;
  struct SubstitutionsFn;
  struct ResultFn;

  ExtensionalityClauseContainer* _extClauses;
};

};

#endif /*__ExtensionalitySubstitution__*/
