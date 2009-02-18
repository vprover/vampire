/**
 * @file ResultSubstitution.cpp
 * Implements class ResultSubstitution.
 */

#include "../Kernel/MMSubstitution.hpp"
#include "../Kernel/RobSubstitution.hpp"

#include "ResultSubstitution.hpp"

namespace Indexing {

using namespace Kernel;

template<class Subst>
class RSProxy
: public ResultSubstitution
{
public:
  RSProxy(Subst* subst, int queryBank, int resultBank)
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
    return proxyToMMSubst(this);
  }

private:
  Subst* _subst;
  int _queryBank;
  int _resultBank;

  template <class S> friend MMSubstitution* proxyToMMSubst(RSProxy<S>* proxy);
};

template<class Subst>
MMSubstitution* proxyToMMSubst(RSProxy<Subst>* proxy)
{
  return 0;
}
template<>
MMSubstitution* proxyToMMSubst(RSProxy<MMSubstitution>* proxy)
{
  return proxy->_subst;
}


ResultSubstitutionSP ResultSubstitution::fromSubstitution(MMSubstitution* s, int queryBank, int resultBank)
{
  return ResultSubstitutionSP(new RSProxy<MMSubstitution>(s, queryBank, resultBank));
}

ResultSubstitutionSP ResultSubstitution::fromSubstitution(RobSubstitution* s, int queryBank, int resultBank)
{
  return ResultSubstitutionSP(new RSProxy<RobSubstitution>(s, queryBank, resultBank));
}

}
