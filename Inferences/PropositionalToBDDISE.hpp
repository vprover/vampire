/**
 * @file PropositionalToBDDISE.hpp
 * Defines class PropositionalToBDDISE.
 */


#ifndef __PropositionalToBDDISE__
#define __PropositionalToBDDISE__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

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
  PropositionalToBDDISE(MainLoop* parent) : _parent(parent) {}
  Clause* simplify(Clause* cl);

  static bool canBddize(Literal* l);
private:
  int getPropPredName(Literal* lit);

  /** Names assigned to propositional predicates */
  DHMap<unsigned, int> _propPredNames;

  MainLoop* _parent;
};

};

#endif /* __PropositionalToBDDISE__ */
