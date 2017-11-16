
/*
 * File Curryfier.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file Curryfier.hpp
 * Defines class Curryfier.
 */


#ifndef __Curryfier__
#define __Curryfier__

#include "Lib/Environment.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/DArray.hpp"
#include "Lib/ArrayMap.hpp"

#include "Indexing/TermSharing.hpp"

#include "Term.hpp"
#include "Signature.hpp"

namespace Kernel {

using namespace Lib;

class Curryfier
{
public:

  TermList curryfy(TermList t)
  {
    if(t.isVar() || (t.isTerm() && t.term()->arity()==0) ) {
      return t;
    }
    Term* trm=t.term();
    if(_termCache.find(trm)) {
      return _termCache.get(trm);
    }
//    TermList res=getCurryFn(trm->functor());
//    TermList *arg=trm->args();
//    while(!arg->isEmpty()) {
//      res=getCurryFn(res,curryfy(*arg));
//      arg=arg->next();
//    }

    TermList res=getCurryFn(trm->functor());
    TermList *arg=trm->args();
    while(!arg->isEmpty()) {
      res=getCurryFn(curryfy(*arg),res);
      arg=arg->next();
    }

//    unsigned arity=trm->arity();
//    TermList res=curryfy(*trm->nthArgument(arity-1));
//    for(int i=arity-2;i>=0;i--) {
//      res=getCurryFn(curryfy(*trm->nthArgument(i)), res);
//    }
//    res=getCurryFn(getCurryFn(trm->functor()), res);
//
//    _termCache.set(trm,res);
    return res;
  }

  static Curryfier* instance()
  {
    static Curryfier* res=0;
    if(!res) {
      res=new Curryfier();
    }
    return res;
  }
private:
  TermList getCurryFn(TermList fn, TermList arg)
  {
    Term* t = new(2) Term;
    t->makeSymbol(_applyFn,2);
    *(t->nthArgument(0))=fn;
    *(t->nthArgument(1))=arg;
    return TermList(env.sharing->insert(t));
  }
  TermList getCurryFn(unsigned function)
  {
    if(!_constantTerms.find(function)) {
      Term* t = new(0) Term;
      t->makeSymbol(_curryConstants[function],0);
      _constantTerms.insert(function,TermList(env.sharing->insert(t)));
    }
    return _constantTerms.get(function);
  }

  Curryfier()
  : _curryConstants(32)
  {
    Signature* sig=env.signature;
    int funCnt=sig->functions();
    _curryConstants.ensure(funCnt);
    _constantTerms.ensure(funCnt);
    for(int i=0;i<funCnt;i++) {
      if(sig->functionArity(i)>0) {
	_curryConstants[i]=sig->addSkolemFunction(0);
      }
    }
    _applyFn=sig->addFunction("@",2);
  }

  unsigned _applyFn;
  DArray<unsigned> _curryConstants;
  ArrayMap<TermList> _constantTerms;
  DHMap<Term*,TermList, PtrIdentityHash > _termCache;
};

};

#endif /* __Curryfier__ */
