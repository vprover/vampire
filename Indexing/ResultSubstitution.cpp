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

#include "ResultSubstitution.hpp"

namespace Indexing {

using namespace Kernel;

class RSProxy
: public ResultSubstitution
{
public:
  USE_ALLOCATOR(RSProxy);
  
  RSProxy(RobSubstitution* subst, int queryBank, int resultBank)
  : _subst(subst), _queryBank(queryBank), _resultBank(resultBank) {}

  TermList applyToQuery(TermList t) final
  { return _subst->apply(t,_queryBank); }
  Literal* applyToQuery(Literal* l) final
  { return _subst->apply(l,_queryBank); }

  TermList applyToResult(TermList t) final
  { return _subst->apply(t,_resultBank); }
  Literal* applyToResult(Literal* l) final
  { return _subst->apply(l,_resultBank); }

  TermList applyTo(TermList t,unsigned index) final
  { return _subst->apply(t,index); }
  Literal* applyTo(Literal* l,unsigned index) final
  { return _subst->apply(l,index); }

  size_t getQueryApplicationWeight(TermList t) final { return _subst->getApplicationResultWeight(t, _queryBank); }
  size_t getQueryApplicationWeight(Literal* l) final { return _subst->getApplicationResultWeight(l, _queryBank); }
  size_t getResultApplicationWeight(TermList t) final { return _subst->getApplicationResultWeight(t, _resultBank); }
  size_t getResultApplicationWeight(Literal* l) final { return _subst->getApplicationResultWeight(l, _resultBank); }


  void output(std::ostream& out) const final { out << *_subst; }

private:
  RobSubstitution* _subst;
  int _queryBank;
  int _resultBank;
};

ResultSubstitutionSP ResultSubstitution::fromSubstitution(RobSubstitution* s, int queryBank, int resultBank)
{ return ResultSubstitutionSP(new RSProxy(s, queryBank, resultBank)); }

} // namespace Indexing
