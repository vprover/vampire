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
  USE_ALLOCATOR(RSProxy);
  
  RSProxy(RobSubstitution* subst, int queryBank, int resultBank)
  : _subst(subst), _queryBank(queryBank), _resultBank(resultBank) {}

  TermList applyToQuery(TermList t) final override
  { return _subst->apply(t,_queryBank); }
  Literal* applyToQuery(Literal* l) final override
  { return _subst->apply(l,_queryBank); }

  TermList applyToResult(TermList t) final override
  { return _subst->apply(t,_resultBank); }
  Literal* applyToResult(Literal* l) final override
  { return _subst->apply(l,_resultBank); }

  TermList applyTo(TermList t,unsigned index) final override
  { return _subst->apply(t,index); }
  Literal* applyTo(Literal* l,unsigned index) final override
  { return _subst->apply(l,index); }

  virtual size_t getQueryApplicationWeight(TermList t) final override { return _subst->getApplicationResultWeight(t, _queryBank); }
  virtual size_t getQueryApplicationWeight(Literal* l) final override { return _subst->getApplicationResultWeight(l, _queryBank); }
  virtual size_t getResultApplicationWeight(TermList t) final override { return _subst->getApplicationResultWeight(t, _resultBank); }
  virtual size_t getResultApplicationWeight(Literal* l) final override { return _subst->getApplicationResultWeight(l, _resultBank); }


  virtual void output(std::ostream& out) const final override { out << *_subst; }

private:
  RobSubstitution* _subst;
  int _queryBank;
  int _resultBank;
};

ResultSubstitutionSP ResultSubstitution::fromSubstitution(RobSubstitution* s, int queryBank, int resultBank)
{ return ResultSubstitutionSP(new RSProxy(s, queryBank, resultBank)); }

} // namespace Indexing
