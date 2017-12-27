
/*
 * File EqualityVariableRemover.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file EqualityVariableRemover.cpp
 * Implements class EqualityVariableRemover.
 */
#if GNUMP
#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/List.hpp"
#include "Lib/RCPtr.hpp"

#include "Kernel/Constraint.hpp"
#include "Kernel/Number.hpp"

#include "Options.hpp"
#include "Statistics.hpp"

#include "EqualityVariableRemover.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

unsigned EqualityVariableRemover::ConstraintHash::hash(const Constraint* c)
{
  CALL("EqualityVariableRemover::ConstraintHash::hash");

  if(c->coeffCnt()==0) {
    return CoeffNumber::hash(c->freeCoeff());
  }
  bool opposite = (*c)[0].isNegative();
  CoeffNumber norm = opposite ? CoeffNumber::minusOne() : CoeffNumber::one();
  unsigned res = CoeffNumber::hash(norm*c->freeCoeff());

  size_t sz = c->coeffCnt();
  for(size_t i=0; i!=sz; i++) {
    res = Hash::combineHashes(res, (*c)[i].var);
    res = Hash::combineHashes(res, CoeffNumber::hash(norm*(*c)[i].value));
  }
  return res;
}
bool EqualityVariableRemover::ConstraintHash::equals(const Constraint* c1, const Constraint* c2)
{
  CALL("EqualityVariableRemover::ConstraintHash::equal");

  if(c1->coeffCnt()!=c2->coeffCnt() || c1->coeffCnt()==0) { return false; }

  size_t sz = c1->coeffCnt();
  for(size_t i=0; i!=sz; i++) {
    if((*c1)[i].var!=(*c2)[i].var) { return false; }
  }
  bool opposite = (*c1)[0].isPositive()!=(*c2)[0].isPositive();
  for(size_t i=0; i<sz; i++) {
    if(opposite) {
      if((*c1)[i].value!=-(*c2)[i].value) { return false; }
    }
    else {
      if((*c1)[i].value!=(*c2)[i].value) { return false; }
    }
  }
  if(opposite) {
    if(c1->freeCoeff()!=-c2->freeCoeff()) { return false; }
  }
  else {
    if(c1->freeCoeff()!=c2->freeCoeff()) { return false; }
  }
  return true;
}


bool EqualityVariableRemover::apply(ConstraintRCList*& lst)
{
  CALL("EqualityVariableRemover::apply");

  scan(lst);

  if(_equalities.isEmpty()) {
    reset();
    return false;
  }

  _v2c.insert(lst);

  Constraint* eliminated = _equalities.getOneKey();
  eliminate(eliminated, lst);

  reset();
  return true;
}

Var EqualityVariableRemover::getEliminatedVariable(Constraint& c)
{
  CALL("EqualityVariableRemover::getEliminatedVariable");
  ASS_G(c.coeffCnt(),0);

  Constraint::CoeffIterator cit = c.coeffs();
  ALWAYS(cit.hasNext());
  Var best = cit.next().var;
  size_t bestConstrCnt = _v2c.getConstraintCnt(best);
  while(cit.hasNext()) {
    Var v = cit.next().var;
    size_t ccnt = _v2c.getConstraintCnt(v);
    if(ccnt<bestConstrCnt) {
      best = v;
      bestConstrCnt = ccnt;
    }
  }
  return best;
}

void EqualityVariableRemover::eliminate(Constraint* c, ConstraintRCList*& lst)
{
  CALL("EqualityVariableRemover::eliminate");

  Constraint* other = _equalities.get(c);
  Var eliminatedVar = getEliminatedVariable(*c);

  Constraint* posEq;
  Constraint* negEq;
  if(c->getCoeff(eliminatedVar).isPositive()) {
    ASS(other->getCoeff(eliminatedVar).isNegative());
    posEq = c;
    negEq = other;
  }
  else {
    ASS(other->getCoeff(eliminatedVar).isPositive());
    posEq = other;
    negEq = c;
  }


  BoundId posId(eliminatedVar, true);
  BoundId negId(eliminatedVar, false);


  for(unsigned i=0; i<2; i++) {
    V2CIndex::Iterator constrIt;
    Constraint* halfEq;
    if(i==0) {
      halfEq = posEq;
      constrIt = _v2c.getConsraintsWithBound(negId);
    }
    else {
      ASS_EQ(i,1);
      halfEq = negEq;
      constrIt = _v2c.getConsraintsWithBound(posId);
    }
    while(constrIt.hasNext()) {
      Constraint* oldConstr = constrIt.next();
      ConstraintRCPtr newConstr(Constraint::resolve(eliminatedVar, *halfEq, *oldConstr, false));
      if(!newConstr->isTautology()) {
	ConstraintRCList::push(newConstr, lst);
      }
    }
  }
  env.statistics->equalityPropagationVariables++;

  static DHSet<Constraint*> toRemove;
  toRemove.reset();
  toRemove.loadFromIterator(_v2c.getConsraintsWithBound(posId));
  toRemove.loadFromIterator(_v2c.getConsraintsWithBound(negId));
  env.statistics->equalityPropagationConstraints += toRemove.size();

  ConstraintRCList::DelIterator cit(lst);
  while(cit.hasNext()) {
    Constraint* c = cit.next().ptr();
    if(toRemove.contains(c)) {
      cit.del();
    }
  }
}

void EqualityVariableRemover::reset()
{
  CALL("EqualityVariableRemover::reset");

  _halves.reset();
  _equalities.reset();
  _v2c.reset();
}

bool EqualityVariableRemover::allowedEquality(Constraint& c)
{
  CALL("EqualityVariableRemover::allowedEquality");

//  return true;
  return c.coeffCnt()<=env.options->bpMaximalPropagatedEqualityLength();
}

void EqualityVariableRemover::scan(ConstraintRCList* lst)
{
  CALL("EqualityVariableRemover::scan");

  ConstraintRCList::Iterator cit(lst);
  while(cit.hasNext()) {
    Constraint* c = cit.next().ptr();

    if(c->coeffCnt()==0 || c->type()!=CT_GREQ) {
      //we ignore constant and strict inequalities
      continue;
    }
    if(!allowedEquality(*c)) {
      continue;
    }

    Constraint* other = _halves.insert(c);
    if(c==other) {
      //we have only one half of equality
      continue;
    }
    if((*c)[0].isPositive()==(*other)[0].isPositive()) {
      //the previous half is the same half
      continue;
    }
    //we insert the @c other constraint into the equality set to avoid
    //duplicities (if we'd insert constraint @c c, we might have mutiple
    //copies of the same equality).
    _equalities.insert(other, c);
  }

}


}
#endif
