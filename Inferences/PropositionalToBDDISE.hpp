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
  void getPropPredName(Literal* lit, int& name, Clause*& premise, bool& newPremise);

  /** Names assigned to propositional predicates */
  DHMap<unsigned, int> _propPredNames;

  /** Clauses to be used as premises for replacing
   * positive predicate occurence by name */
  DHMap<unsigned, Clause*> _propPredPosNamePremises;

  /** Clauses to be used as premises for replacing
   * negative predicate occurence by name */
  DHMap<unsigned, Clause*> _propPredNegNamePremises;

};

};

#endif /* __PropositionalToBDDISE__ */
