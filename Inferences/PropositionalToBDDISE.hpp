/**
 * @file PropositionalToBDDISE.hpp
 * Defines class PropositionalToBDDISE.
 */


#ifndef __PropositionalToBDDISE__
#define __PropositionalToBDDISE__

#include "../Forwards.hpp"

#include "../Lib/DHMap.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

/**
 * Moves propositional literals into the propositional part of the clause (i.e. BDD).
 *
 * Unlike other ImmediateSimplificationEngine objects, this one assigns the
 * propositional part of the clause.
 */
class PropositionalToBDDISE
: public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* cl);

private:
  bool canBddize(Literal* l);
  int getPropPredName(Literal* lit);

  /** Names assigned to propositional predicates */
  DHMap<unsigned, int> _propPredNames;
};

};

#endif /* __PropositionalToBDDISE__ */
