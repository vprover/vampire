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
  
  RSProxy(RobSubstitutionTL* subst, VarBank queryBank, VarBank resultBank)
  : _subst(subst), _queryBank(queryBank), _resultBank(resultBank) {}

  TermList applyToQuery(TermList t) override
  { return _subst->apply(t,_queryBank); }
  Literal* applyToQuery(Literal* l) override
  { return _subst->apply(l,_queryBank); }

  TermList applyToResult(TermList t) override
  { return _subst->apply(t,_resultBank); }
  Literal* applyToResult(Literal* l) override
  { return _subst->apply(l,_resultBank); }

  TermList applyTo(TermList t,VarBank bank) override
  { return _subst->apply(t,bank); }
  Literal* applyTo(Literal* l,VarBank bank) override
  { return _subst->apply(l,bank); }

  virtual size_t getQueryApplicationWeight(TermList t) override { return _subst->getApplicationResultWeight(t, _queryBank); }
  virtual size_t getQueryApplicationWeight(Literal* l) override { return _subst->getApplicationResultWeight(l, _queryBank); }
  virtual size_t getResultApplicationWeight(TermList t) override { return _subst->getApplicationResultWeight(t, _resultBank); }
  virtual size_t getResultApplicationWeight(Literal* l) override { return _subst->getApplicationResultWeight(l, _resultBank); }

  virtual void output(std::ostream& out) const final override { out << *_subst; }

  /** return iterator over constraints */
  virtual Recycled<LiteralStack> getConstraints() override { return _subst->constraints(); }
  virtual bool isIdentityOnQueryWhenResultBound() override { return _subst->outputBank() == _queryBank;}
  virtual bool isIdentityOnResultWhenQueryBound() override { return _subst->outputBank() == _resultBank;}

private:
  RobSubstitutionTL* _subst;
  VarBank _queryBank;
  VarBank _resultBank;
};

ResultSubstitutionSP ResultSubstitution::fromSubstitution(RobSubstitutionTL* s, VarBank queryBank, VarBank resultBank)
{ return ResultSubstitutionSP(new RSProxy(s, queryBank, resultBank)); }

/**
 * Test whether this substitution object is a renaming on the variables of @param t
 * @param result indicates whether we mean the "bank" applied 
 * to a result term or a query one (cf. applyToQuery/applyToResult)
 */
bool ResultSubstitution::isRenamingOn(TermList t, bool result) 
{
  CALL("ResultSubstitution::isRenamingOn");

  DHMap<TermList,TermList> renamingInMaking;

  VariableIterator it(t);
  while(it.hasNext()) {
    TermList v = it.next();
    ASS(v.isVar());

    TermList vSubst;
    if (result) {
      ASS(isIdentityOnQueryWhenResultBound());
      // code trees don't implement general apply, but satisfy the assertion which makes the following OK
      vSubst = applyToBoundResult(v);
    } else {
      ASS(isIdentityOnResultWhenQueryBound());
      // the above holds, for a change, for the used substitution trees
      vSubst = applyToBoundQuery(v);
    }
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

} // namespace Indexing
