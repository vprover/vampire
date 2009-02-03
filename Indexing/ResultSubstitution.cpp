/**
 * @file ResultSubstitution.cpp
 * Implements class ResultSubstitution.
 */

#include "../Kernel/MMSubstitution.hpp"

#include "ResultSubstitution.hpp"

namespace Indexing {

using namespace Kernel;

class MMResultSubstitution
: public ResultSubstitution
{
public:
  MMResultSubstitution(MMSubstitution* subst, int queryBank, int resultBank)
  : _subst(subst), _queryBank(queryBank), _resultBank(resultBank) {}

  TermList applyToQuery(TermList t)
  { return _subst->apply(t,_queryBank); }
  Literal* applyToQuery(Literal* l)
  { return _subst->apply(l,_queryBank); }

  TermList applyToResult(TermList t)
  { return _subst->apply(t,_resultBank); }
  Literal* applyToResult(Literal* l)
  { return _subst->apply(l,_resultBank); }

  virtual MMSubstitution* tryGetMMSubstitution()
  {
    return _subst;
  }

private:
  MMSubstitution* _subst;
  int _queryBank;
  int _resultBank;
};

ResultSubstitutionSP ResultSubstitution::fromMMSubstitution(MMSubstitution* s, int queryBank, int resultBank)
{
  return ResultSubstitutionSP(new MMResultSubstitution(s, queryBank, resultBank));
}

}
