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

  virtual size_t getQueryApplicationWeight(TermList t) { return _subst->getApplicationResultWeight(t, _queryBank); }
  virtual size_t getQueryApplicationWeight(Literal* l) { return _subst->getApplicationResultWeight(l, _queryBank); }
  virtual size_t getResultApplicationWeight(TermList t) { return _subst->getApplicationResultWeight(t, _resultBank); }
  virtual size_t getResultApplicationWeight(Literal* l) { return _subst->getApplicationResultWeight(l, _resultBank); }

  RobSubstitution* tryGetRobSubstitution() { return _subst; }

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
  Applicator(bool isQuery) : _isQuery(isQuery) {}

  TermList apply(int var)
  {
    unsigned resVarNum;
    if(_isQuery) {
      resVarNum = var*2;
    }
    else {
      resVarNum = var*2+1;
    }
    return TermList(resVarNum,false);
  }
private:
  bool _isQuery;
};

TermList DisjunctQueryAndResultVariablesSubstitution::applyToQuery(TermList t)
{
  CALL("DisjunctQueryAndResultVariablesSubstitution::applyToQuery");

  Applicator apl(true);
  return SubstHelper::apply(t, apl);
}

Literal* DisjunctQueryAndResultVariablesSubstitution::applyToQuery(Literal* l)
{
  CALL("DisjunctQueryAndResultVariablesSubstitution::applyToQuery(Literal*)");

  Applicator apl(true);
  return SubstHelper::apply(l, apl);
}

TermList DisjunctQueryAndResultVariablesSubstitution::applyToResult(TermList t)
{
  CALL("DisjunctQueryAndResultVariablesSubstitution::applyToResult");

  Applicator apl(false);
  return SubstHelper::apply(t, apl);
}

Literal* DisjunctQueryAndResultVariablesSubstitution::applyToResult(Literal* l)
{
  CALL("DisjunctQueryAndResultVariablesSubstitution::applyToResult");

  Applicator apl(false);
  return SubstHelper::apply(l, apl);
}




}
