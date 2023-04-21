/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file ResultSubstitution.cpp
 * Implements class ResultSubstitution.
 */

#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "ResultSubstitution.hpp"

namespace Indexing {

using namespace Kernel;

class RSProxy
: public ResultSubstitution
{
public:
  CLASS_NAME(RSProxy);
  USE_ALLOCATOR(RSProxy);
  
  RSProxy(RobSubstitution* subst, int queryBank, int resultBank)
  : _subst(subst), _queryBank(queryBank), _resultBank(resultBank) {}

  TermList applyToQuery(TermList t) override { return _subst->apply(t,_queryBank); }
  Literal* applyToQuery(Literal* l) override { return _subst->apply(l,_queryBank); }

  TermList applyToResult(TermList t) override { return _subst->apply(t,_resultBank); }
  Literal* applyToResult(Literal* l) override { return _subst->apply(l,_resultBank); }

  virtual size_t getQueryApplicationWeight(TermList t) override { return _subst->getApplicationResultWeight(t, _queryBank); }
  virtual size_t getQueryApplicationWeight(Literal* l) override { return _subst->getApplicationResultWeight(l, _queryBank); }
  virtual size_t getResultApplicationWeight(TermList t) override { return _subst->getApplicationResultWeight(t, _resultBank); }
  virtual size_t getResultApplicationWeight(Literal* l) override { return _subst->getApplicationResultWeight(l, _resultBank); }

  virtual void output(std::ostream& out) const final override { out << *_subst; }

private:
  RobSubstitution* _subst;
  int _queryBank;
  int _resultBank;
};

ResultSubstitutionSP ResultSubstitution::fromSubstitution(RobSubstitution* s, int queryBank, int resultBank)
{ return ResultSubstitutionSP(new RSProxy(s, queryBank, resultBank)); }

/** Test whether the function sigma is a renaming on the variables of @param t */
template<class Sigma>
bool isRenamingOn(Sigma sigma, TermList t)
{
  CALL("isRenamingOn");

  DHMap<TermList,TermList> renamingInMaking;

  VariableIterator it(t);
  while(it.hasNext()) {
    TermList v = it.next();
    ASS(v.isVar());

    TermList vSubst = sigma(v);
    if (!vSubst.isVar()) {
      return false;
    }
    TermList vStored;
    if (!renamingInMaking.findOrInsert(v,vStored,vSubst) && vStored != vSubst) {
      return false;
    }
  }
  return true;
}

/**
 * This is a copy paste version of ResultSubsition::isRenamingOn, instantiated for result = true.
 */
bool GenSubstitution::isRenamingOnResult(TermList t) 
{
  CALL("ResultSubstitution::isRenamingOn");
  return isRenamingOn([this](TermList t) { return applyToBoundResult(t); }, t);
}

/**
 * This is a copy paste version of ResultSubsition::isRenamingOn, instantiated for result = false.
 */
bool InstSubstitution::isRenamingOnQuery(TermList t) 
{
  CALL("ResultSubstitution::isRenamingOn");
  return isRenamingOn([this](TermList t) { return applyToBoundQuery(t); }, t);
}

} // namespace Indexing
