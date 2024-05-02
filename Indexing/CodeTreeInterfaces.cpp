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
 * @file CodeTreeInterfaces.cpp
 * Implements indexing structures that use code trees.
 *
 */

#include "Indexing/Index.hpp"
#include "Indexing/ResultSubstitution.hpp"
#include "Lib/Allocator.hpp"
#include "Lib/Recycled.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Renaming.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"

#include "ClauseCodeTree.hpp"
#include "TermCodeTree.hpp"

#include "CodeTreeInterfaces.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

class CodeTreeSubstitution
: public ResultSubstitution
{
public:
  CodeTreeSubstitution(CodeTree::BindingArray* bindings, Renaming* resultNormalizer)
  : _bindings(bindings), _resultNormalizer(resultNormalizer)
  {}

  USE_ALLOCATOR(CodeTreeSubstitution);

  TermList apply(unsigned var)
  {
    ASS(_resultNormalizer->contains(var));
    unsigned nvar=_resultNormalizer->get(var);
    TermList res=(*_bindings)[nvar];
    ASS(res.isTerm()||res.isOrdinaryVar());
    ASSERT_VALID(res);
    return res;
  }

  TermList applyToBoundResult(unsigned v) override
  {
    return apply(v);
  }

  TermList applyToBoundResult(TermList t) override
  {
    return SubstHelper::apply(t, *this);
  }

  Literal* applyToBoundResult(Literal* lit) override
  {
    return SubstHelper::apply(lit, *this);
  }

  bool isIdentityOnQueryWhenResultBound() override {return true;}
private:
  virtual void output(std::ostream& out) const final override 
  { out << "CodeTreeSubstitution(<output unimplemented>)"; }

  CodeTree::BindingArray* _bindings;
  Renaming* _resultNormalizer;
};

///////////////////////////////////////


class CodeTreeTIS::ResultIterator
: public IteratorCore<QueryRes<ResultSubstitutionSP, TermLiteralClause>>
{
public:
  ResultIterator(CodeTreeTIS* tree, TermList t, bool retrieveSubstitutions)
  : _retrieveSubstitutions(retrieveSubstitutions),
    _found(0), _finished(false), _tree(tree)
  {
    _matcher->init(&_tree->_ct, t);

    if(_retrieveSubstitutions) {
      _subst = new CodeTreeSubstitution(&_matcher->bindings, &*_resultNormalizer);
    }
  }

  ~ResultIterator()
  {
    if(_retrieveSubstitutions) {
      delete _subst;
    }
  }

  USE_ALLOCATOR(ResultIterator);

  bool hasNext()
  {
    if(_found) {
      return true;
    }
    if(_finished) {
      return false;
    }
    void* data=_matcher->next();
    _found=static_cast<TermCodeTree::TermInfo*>(data);
    if(!_found) {
      _finished=true;
    }
    return _found;
  }

  QueryRes<ResultSubstitutionSP, TermLiteralClause> next()
  {
    ASS(_found);

    ResultSubstitutionSP subs;
    if (_retrieveSubstitutions) {
      _resultNormalizer->reset();
      _resultNormalizer->normalizeVariables(_found->term);
      subs = ResultSubstitutionSP(_subst, /* nondisposable */ true);
    }
    auto out = QueryRes<ResultSubstitutionSP, TermLiteralClause>(subs, _found);
    _found=0;
    return out;
  }
private:

  CodeTreeSubstitution* _subst;
  Recycled<Renaming> _resultNormalizer;
  bool _retrieveSubstitutions;
  TermCodeTree::TermInfo* _found;
  bool _finished;
  CodeTreeTIS* _tree;
  Recycled<TermCodeTree::TermMatcher> _matcher;
};

void CodeTreeTIS::_insert(TypedTermList t, Literal* lit, Clause* cls)
{
  auto ti = new TermLiteralClause{ t,lit,cls };
  _ct.insert(ti);
}

void CodeTreeTIS::_remove(TypedTermList t, Literal* lit, Clause* cls)
{
  _ct.remove(TermLiteralClause{ t,lit,cls });
}

VirtualIterator<QueryRes<ResultSubstitutionSP, TermLiteralClause>> CodeTreeTIS::getGeneralizations(TypedTermList t, bool retrieveSubstitutions)
{
  if(_ct.isEmpty()) {
    return VirtualIterator<QueryRes<ResultSubstitutionSP, TermLiteralClause>>::getEmpty();
  }

  return vi( new ResultIterator(this, t, retrieveSubstitutions) );
}

bool CodeTreeTIS::generalizationExists(TermList t)
{
  if(_ct.isEmpty()) {
    return false;
  }

  static TermCodeTree::TermMatcher tm;
  
  tm.init(&_ct, t);
  bool res=tm.next();
  tm.reset();
  
  return res;
}

/////////////////   CodeTreeSubsumptionIndex   //////////////////////

void CodeTreeSubsumptionIndex::handleClause(Clause* cl, bool adding)
{
  TIME_TRACE("codetree subsumption index maintanance");

  if(adding) {
    _ct.insert(cl);
  }
  else {
    _ct.remove(cl);
  }
}

}






























