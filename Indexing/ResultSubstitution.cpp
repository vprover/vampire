/**
 * @file ResultSubstitution.cpp
 * Implements class ResultSubstitution.
 */

#include "Kernel/RobSubstitution.hpp"
#include "Kernel/EGSubstitution.hpp"

#include "ResultSubstitution.hpp"

namespace Indexing {

using namespace Kernel;

class RSProxy
: public ResultSubstitution
{
public:
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

//class EGSProxy
//: public ResultSubstitution
//{
//public:
//  EGSProxy(EGSubstitution* subst, int queryBank, int resultBank)
//  : _subst(subst), _queryBank(queryBank), _resultBank(resultBank) {}
//
//  TermList applyToQuery(TermList t)
//  { return _subst->apply(t,_queryBank); }
//  Literal* applyToQuery(Literal* l)
//  { return _subst->apply(l,_queryBank); }
//
//  TermList applyToResult(TermList t)
//  { return _subst->apply(t,_resultBank); }
//  Literal* applyToResult(Literal* l)
//  { return _subst->apply(l,_resultBank); }
//
//  RobSubstitution* tryGetRobSubstitution() { return 0; }
//
//private:
//  EGSubstitution* _subst;
//  int _queryBank;
//  int _resultBank;
//};
//
//ResultSubstitutionSP ResultSubstitution::fromSubstitution(EGSubstitution* s, int queryBank, int resultBank)
//{
//  return ResultSubstitutionSP(new EGSProxy(s, queryBank, resultBank));
//}

}
