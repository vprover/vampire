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

  TermList applyToQuery(TermList t)
  { return _subst->apply(t,_queryBank); }
  Literal* applyToQuery(Literal* l)
  { return _subst->apply(l,_queryBank); }

  TermList applyToResult(TermList t)
  { return _subst->apply(t,_resultBank); }
  Literal* applyToResult(Literal* l)
  { return _subst->apply(l,_resultBank); }

  TermList applyTo(TermList t,unsigned index)
  { return _subst->apply(t,index); }
  Literal* applyTo(Literal* l,unsigned index)
  { return _subst->apply(l,index); }

  virtual size_t getQueryApplicationWeight(TermList t) { return _subst->getApplicationResultWeight(t, _queryBank); }
  virtual size_t getQueryApplicationWeight(Literal* l) { return _subst->getApplicationResultWeight(l, _queryBank); }
  virtual size_t getResultApplicationWeight(TermList t) { return _subst->getApplicationResultWeight(t, _resultBank); }
  virtual size_t getResultApplicationWeight(Literal* l) { return _subst->getApplicationResultWeight(l, _resultBank); }

  RobSubstitution* tryGetRobSubstitution() { return _subst; }

#if VDEBUG
  vstring toStringDeref(bool deref){ return _subst->toString(deref); }
#endif

private:
  RobSubstitution* _subst;
  int _queryBank;
  int _resultBank;
};

ResultSubstitutionSP ResultSubstitution::fromSubstitution(RobSubstitution* s, int queryBank, int resultBank)
{
  return ResultSubstitutionSP(new RSProxy(s, queryBank, resultBank));
}


/////////////////////////
// IdentitySubstitution
//

ResultSubstitutionSP IdentitySubstitution::instance()
{
  CALL("IdentitySubstitution::instance");

  static ResultSubstitutionSP inst = ResultSubstitutionSP(new IdentitySubstitution());

  return inst;
}

////////////////////////////////////////////////
// DisjunctQueryAndResultVariablesSubstitution
//

struct DisjunctQueryAndResultVariablesSubstitution::Applicator
{
  Applicator(bool isQuery, Renaming& renaming) : _isQuery(isQuery), _renaming(renaming) {}

  TermList apply(int var)
  {
    unsigned resVarNum;

    // rename Result and Query apart
    if(_isQuery) {
      resVarNum = var*2;
    }
    else {
      resVarNum = var*2+1;
    }

    // normalize using renaming (to keep the variables small)
    resVarNum = _renaming.getOrBind(resVarNum);

    TermList res = TermList(resVarNum,false);

    // check there was no (obvious) overflow
    ASS_EQ(resVarNum,res.var());

    return res;
  }
private:
  bool _isQuery;
  Renaming& _renaming;
};

TermList DisjunctQueryAndResultVariablesSubstitution::applyToQuery(TermList t)
{
  CALL("DisjunctQueryAndResultVariablesSubstitution::applyToQuery");

  Applicator apl(true,_renaming);
  return SubstHelper::apply(t, apl);
}

Literal* DisjunctQueryAndResultVariablesSubstitution::applyToQuery(Literal* l)
{
  CALL("DisjunctQueryAndResultVariablesSubstitution::applyToQuery(Literal*)");

  Applicator apl(true,_renaming);
  return SubstHelper::apply(l, apl);
}

TermList DisjunctQueryAndResultVariablesSubstitution::applyToResult(TermList t)
{
  CALL("DisjunctQueryAndResultVariablesSubstitution::applyToResult");

  Applicator apl(false,_renaming);
  return SubstHelper::apply(t, apl);
}

Literal* DisjunctQueryAndResultVariablesSubstitution::applyToResult(Literal* l)
{
  CALL("DisjunctQueryAndResultVariablesSubstitution::applyToResult");

  Applicator apl(false,_renaming);
  return SubstHelper::apply(l, apl);
}




}
