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

#include "Lib/Allocator.hpp"
#include "Lib/Recycler.hpp"
#include "Lib/TimeCounter.hpp"
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
  : _bindings(bindings), _resultNormalizer(resultNormalizer),
  _applicator(0)
  {}
  ~CodeTreeSubstitution()
  {
    if(_applicator) {
      delete _applicator;
    }
  }

  CLASS_NAME(CodeTreeSubstitution);
  USE_ALLOCATOR(CodeTreeSubstitution);

  TermList applyToBoundResult(TermList t)
  {
    CALL("CodeTreeSubstitution::applyToBoundResult(TermList)");
    return SubstHelper::apply(t, *getApplicator());
  }

  Literal* applyToBoundResult(Literal* lit)
  {
    CALL("CodeTreeSubstitution::applyToBoundResult(Literal*)");
    return SubstHelper::apply(lit, *getApplicator());
  }

  bool isIdentityOnQueryWhenResultBound() {return true;}
private:
  struct Applicator
  {
    inline
    Applicator(CodeTree::BindingArray* bindings, Renaming* resultNormalizer)
    : _bindings(bindings), _resultNormalizer(resultNormalizer) {}

    TermList apply(unsigned var)
    {
      ASS(_resultNormalizer->contains(var));
      unsigned nvar=_resultNormalizer->get(var);
      TermList res=(*_bindings)[nvar];
      ASS(res.isTerm()||res.isOrdinaryVar());
      ASSERT_VALID(res);
      return res;
    }

    CLASS_NAME(CodeTreeSubstitution::Applicator);
    USE_ALLOCATOR(Applicator);
  private:
    CodeTree::BindingArray* _bindings;
    Renaming* _resultNormalizer;
  };

  Applicator* getApplicator()
  {
    if(!_applicator) {
      _applicator=new Applicator(_bindings, _resultNormalizer);
    }
    return _applicator;
  }

  CodeTree::BindingArray* _bindings;
  Renaming* _resultNormalizer;
  Applicator* _applicator;
};

///////////////////////////////////////


class CodeTreeTIS::ResultIterator
: public IteratorCore<TermQueryResult>
{
public:
  ResultIterator(CodeTreeTIS* tree, TermList t, bool retrieveSubstitutions)
  : _retrieveSubstitutions(retrieveSubstitutions),
    _found(0), _finished(false), _tree(tree)
  {
    Recycler::get(_matcher);
    _matcher->init(&_tree->_ct, t);

    if(_retrieveSubstitutions) {
      Recycler::get(_resultNormalizer);
      _subst=new CodeTreeSubstitution(&_matcher->bindings, _resultNormalizer);
    }
  }

  ~ResultIterator()
  {
    _matcher->deinit();
    Recycler::release(_matcher);
    if(_retrieveSubstitutions) {
      Recycler::release(_resultNormalizer);
      delete _subst;
    }
  }

  CLASS_NAME(CodeTreeTIS::ResultIterator);
  USE_ALLOCATOR(ResultIterator);

  bool hasNext()
  {
    CALL("CodeTreeTIS::ResultIterator::hasNext");

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

  TermQueryResult next()
  {
    CALL("CodeTreeTIS::ResultIterator::next");
    ASS(_found);

    TermQueryResult res;
    if(_retrieveSubstitutions) {
      _resultNormalizer->reset();
      _resultNormalizer->normalizeVariables(_found->t);
      res=TermQueryResult(_found->t, _found->lit, _found->cls,
	  ResultSubstitutionSP(_subst,true));
    }
    else {
      res=TermQueryResult(_found->t, _found->lit, _found->cls);
    }
    _found=0;
    return res;
  }
private:

  CodeTreeSubstitution* _subst;
  Renaming* _resultNormalizer;
  bool _retrieveSubstitutions;
  TermCodeTree::TermInfo* _found;
  bool _finished;
  CodeTreeTIS* _tree;
  TermCodeTree::TermMatcher* _matcher;
};

void CodeTreeTIS::insert(TermList t, Literal* lit, Clause* cls)
{
  CALL("CodeTreeTIS::insert");

  TermCodeTree::TermInfo* ti=new TermCodeTree::TermInfo(t,lit,cls);
  _ct.insert(ti);
}

void CodeTreeTIS::remove(TermList t, Literal* lit, Clause* cls)
{
  CALL("CodeTreeTIS::remove");
  
  _ct.remove(TermCodeTree::TermInfo(t,lit,cls));
}

TermQueryResultIterator CodeTreeTIS::getGeneralizations(TermList t, bool retrieveSubstitutions)
{
  CALL("CodeTreeTIS::getGeneralizations");

  if(_ct.isEmpty()) {
    return TermQueryResultIterator::getEmpty();
  }

  return vi( new ResultIterator(this, t, retrieveSubstitutions) );
}

bool CodeTreeTIS::generalizationExists(TermList t)
{
  CALL("CodeTreeTIS::generalizationExists");

  if(_ct.isEmpty()) {
    return false;
  }

  static TermCodeTree::TermMatcher tm;
  
  tm.init(&_ct, t);
  bool res=tm.next();
  tm.deinit();
  
  return res;
}

// struct CodeTreeLIS::LiteralInfo
// {
//   LiteralInfo(Literal* lit, Clause* cls)
//   : lit(lit), cls(cls) {}

//   inline bool operator==(const LiteralInfo& o)
//   { return cls==o.cls && lit==o.lit; }

//   inline bool operator!=(const LiteralInfo& o)
//   { return !(*this==o); }

//   CLASS_NAME(CodeTreeLIS::LiteralInfo);
//   USE_ALLOCATOR(LiteralInfo);

//   Literal* lit;
//   Clause* cls;
// };

// class CodeTreeLIS::ResultIterator
// : public IteratorCore<SLQueryResult>
// {
// public:
//   ResultIterator(CodeTreeLIS* tree, Literal* lit, bool complementary,
//       bool retrieveSubstitutions)
//   : _canReorder(lit->commutative()),
//     _retrieveSubstitutions(retrieveSubstitutions),
//     _found(0), _finished(false), _tree(tree)
//   {
//     _flatTerm=FlatTerm::create(lit);
//     if(complementary) {
//       _flatTerm->changeLiteralPolarity();
//     }

//     Recycler::get(_ctx);
//     _ctx->init(_flatTerm,&_tree->_ct);

//     if(_retrieveSubstitutions) {
//       Recycler::get(_resultNormalizer);
//       _subst=new CodeTreeSubstitution(_ctx, _resultNormalizer);
//     }
//   }

//   ~ResultIterator()
//   {
//     _ctx->deinit(&_tree->_ct);
//     Recycler::release(_ctx);
//     if(_retrieveSubstitutions) {
//       Recycler::release(_resultNormalizer);
//       delete _subst;
//     }
//     _flatTerm->destroy();
//   }

//   CLASS_NAME(CodeTreeLIS::ResultIterator);
//   USE_ALLOCATOR(ResultIterator);

//   bool hasNext()
//   {
//     CALL("CodeTreeLIS::ResultIterator::hasNext");

//     if(_found) {
//       return true;
//     }
//     if(_finished) {
//       return false;
//     }

//   retry_search:
//     void* data;
//     if(TermCodeTree::next(*_ctx, data)) {
//       _found=static_cast<LiteralInfo*>(data);
//     }
//     else {
//       if(_canReorder) {
// 	_canReorder=false;
// 	_ctx->deinit(&_tree->_ct);
// 	_flatTerm->swapCommutativePredicateArguments();
// 	_ctx->init(_flatTerm,&_tree->_ct);
// 	goto retry_search;
//       }
//       _found=0;
//       _finished=true;
//     }
//     return _found;
//   }

//   SLQueryResult next()
//   {
//     CALL("CodeTreeLIS::ResultIterator::next");
//     ASS(_found);

//     SLQueryResult res;
//     if(_retrieveSubstitutions) {
//       _resultNormalizer->reset();
//       _resultNormalizer->normalizeVariables(_found->lit);
//       res=SLQueryResult(_found->lit, _found->cls,
// 	  ResultSubstitutionSP(_subst,true));
//     }
//     else {
//       res=SLQueryResult(_found->lit, _found->cls);
//     }
//     _found=0;
//     return res;
//   }
// private:
//   /** True if the query literal is commutative and we still
//    * may try swaping its arguments /
//   bool _canReorder;
//   FlatTerm* _flatTerm;
//   CodeTreeSubstitution* _subst;
//   Renaming* _resultNormalizer;
//   bool _retrieveSubstitutions;
//   LiteralInfo* _found;
//   bool _finished;
//   CodeTreeLIS* _tree;
//   TermCodeTree::TermEContext* _ctx;
// };

// void CodeTreeLIS::insert(Literal* lit, Clause* cls)
// {
//   CALL("CodeTreeLIS::insert");
//   ASS_EQ(_ct._initEContextCounter,0); //index must not be modified while traversed

//   static CodeTree::CodeStack code;
//   code.reset();

//   _ct.compile(lit,code);
//   ASS(code.top().isSuccess());

//   //assign the term info
//   code.top().result=new LiteralInfo(lit,cls);
//   ASS(code.top().isSuccess());

//   _ct.incorporate(code);
// }

// void CodeTreeLIS::remove(Literal* lit, Clause* cls)
// {
//   CALL("CodeTreeLIS::remove");
//   ASS_EQ(_ct._initEContextCounter,0); //index must not be modified while traversed

//   LiteralInfo li(lit,cls);

//   static TermCodeTree::TermEContext ctx;
//   ctx.init(lit, &_ct);

//   EqualityDerefFn<LiteralInfo> succFn(&li);
//   CodeTree::remove(ctx, &_ct, &succFn);

//   ctx.deinit(&_ct);
// }

// SLQueryResultIterator CodeTreeLIS::getGeneralizations(Literal* lit,
// 	  bool complementary, bool retrieveSubstitutions)
// {
//   CALL("CodeTreeLIS::getGeneralizations");

//   if(_ct.isEmpty()) {
//     return SLQueryResultIterator::getEmpty();
//   }

//   return vi( new ResultIterator(this, lit, complementary,
//       retrieveSubstitutions) );
// }

/////////////////   CodeTreeSubsumptionIndex   //////////////////////

class CodeTreeSubsumptionIndex::ClauseSResIterator
: public IteratorCore<ClauseSResQueryResult>
{
public:
  ClauseSResIterator(ClauseCodeTree* tree, Clause* query, bool sres)
  : ready(false)
  {
    Recycler::get(cm);
    cm->init(tree, query, sres);
  }
  ~ClauseSResIterator()
  {
    cm->deinit();
    Recycler::release(cm);
  }
  
  bool hasNext()
  {
    CALL("CodeTreeSubsumptionIndex::ClauseSResIterator::hasNext");
    if(ready) {
      return result;
    }
    ready=true;
    result=cm->next(resolvedQueryLit);
    ASS(!result || resolvedQueryLit<1000000);
    return result;
  }
  
  ClauseSResQueryResult next()
  {
    CALL("CodeTreeSubsumptionIndex::ClauseSResIterator::next");
    ASS(result);
    
    ready=false;
    if(resolvedQueryLit==-1) {
      return ClauseSResQueryResult(result);
    }
    else {
      return ClauseSResQueryResult(result, resolvedQueryLit);
    }
  }
private:
  bool ready;
  Clause* result;
  int resolvedQueryLit;
  ClauseCodeTree::ClauseMatcher* cm;
};

void CodeTreeSubsumptionIndex::handleClause(Clause* cl, bool adding)
{
  CALL("CodeTreeSubsumptionIndex::handleClause");
  
  TimeCounter tc(TC_FORWARD_SUBSUMPTION_INDEX_MAINTENANCE);

  if(adding) {
    _ct.insert(cl);
  }
  else {
    _ct.remove(cl);
  }
}

ClauseSResResultIterator CodeTreeSubsumptionIndex
	::getSubsumingOrSResolvingClauses(Clause* cl, bool subsumptionResolution)
{
  CALL("CodeTreeSubsumptionIndex::getSubsumingClauses");

  if(_ct.isEmpty()) {
    return ClauseSResResultIterator::getEmpty();
  }

  return vi( new ClauseSResIterator(&_ct, cl, subsumptionResolution) );
}


}






























