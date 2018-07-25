
/*
 * File Matcher.hpp.
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
 * @file Matcher.hpp
 * Defines class Matcher.
 */


#ifndef __Matcher__
#define __Matcher__

#include "Forwards.hpp"

#include "Lib/Backtrackable.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Hash.hpp"
#include "Lib/Stack.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Signature.hpp"

#include "Substitution.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"

namespace Kernel {

using namespace Lib;

class MatchingUtils
{
public:
  static TermList getInstanceFromMatch(TermList matchedBase,
      TermList matchedInstance, TermList resultBase);
  static Formula* getInstanceFromMatch(Literal* matchedBase,
      Literal* matchedInstance, Formula* resultBase);

  static bool isVariant(Literal* l1, Literal* l2, bool complementary=false);

  static bool haveReversedVariantArgs(Term* l1, Term* l2);
  static bool haveVariantArgs(Term* l1, Term* l2);

  static bool match(Literal* base, Literal* instance, bool complementary)
  {
    CALL("MatchingUtils::match");

    static MapBinder binder;
    return match(base, instance, complementary, binder);
  }

  /**
   * Matches two literals, using @b binder to store and check bindings
   * of base variables. @b binder must be a functor with parameters
   * (unsigned var, TermList term), that in case variable @b var is
   * unbound, binds it to @b term and returns true, if @b var is
   * bound, returns true iff it is bound to @b term. @b binder also
   * must contain function reset() that resets the binding. The
   * @b binder is reset by the function also for the first time if
   * needed.
   */
  template<class Binder>
  static bool match(Literal* base, Literal* instance, bool complementary, Binder& binder)
  {
    CALL("MatchingUtils::match(Literal*, Literal*, bool, Binder&)");

    if(!Literal::headersMatch(base,instance,complementary)) {
      return false;
    }

    if(base->arity()==0) {
      return true;
    }

    binder.reset();

    if(base->commutative()) {
      ASS(base->arity()==2);
      if(matchArgs(base, instance, binder)) {
	return true;
      }
      binder.reset();
      return matchTerms(*base->nthArgument(0), *instance->nthArgument(1), binder) &&
	matchTerms(*base->nthArgument(1), *instance->nthArgument(0), binder);
    } else {
      return matchArgs(base, instance, binder);
    }
  }

  static bool matchReversedArgs(Literal* base, Literal* instance);
  static bool matchArgs(Term* base, Term* instance);
  static bool matchTerms(TermList base, TermList instance);

  template<class Binder>
  static bool matchTerms(TermList base, TermList instance, Binder& binder)
  {
    CALL("MatchingUtils::matchTerms/3");

    if(base.isTerm()) {
      Term* bt=base.term();
      if(!instance.isTerm() || base.term()->functor()!=instance.term()->functor()) {
	return false;
      }
      Term* it=instance.term();
      if(bt->shared() && it->shared()) {
        if(bt->ground()) {
          return bt==it;
        }
        if(bt->weight() > it->weight()) {
          return false;
        }
      }
      ASS_G(base.term()->arity(),0);
      return matchArgs(base.term(), instance.term(), binder);
    } else {
      ASS(base.isOrdinaryVar());
      return binder.bind(base.var(), instance);
    }
  }

  template<class Binder>
  static bool matchArgs(Term* base, Term* instance, Binder& binder);

  template<class Map>
  struct MapRefBinder
  {
    MapRefBinder(Map& map) : _map(map) {}

    bool bind(unsigned var, TermList term)
    {
      TermList* aux;
      return _map.getValuePtr(var,aux,term) || *aux==term;
    }
    void specVar(unsigned var, TermList term)
    { ASSERTION_VIOLATION; }
    void reset() { _map.reset(); }
  private:
    Map& _map;
  };

  inline
  static OperatorType* getFunctorType(const Term* t){
    if(t->hasVarHead()){
      return env.signature->getVarType(t->functor());
    }
    return env.signature->getFunction(t->functor())->fnType();
  }


  static bool hasMatchableVarHead(TermList base, TermList inst){
    CALL("MatchingUtils::hasMatchableVarHead");

    if(!(base.isTerm() && inst.isTerm())){
      return false;
    }

    Term* baseT = base.term();
    Term* instT = inst.term();

    ASS(baseT->hasVarHead());

    OperatorType* baseType = getFunctorType(baseT);
    OperatorType* instType = getFunctorType(instT);
    
    return baseType->isSuffix(instType);
  }

  // Function getPrefix should only be called after a call
  // to hasMatchableVarHead. Returns the prefix substituion 
  // for the variable head to unify terms.
  static Prefix getPrefix(TermList base, TermList inst){
    CALL("MatchingUtils::getPrefix");

    ASS(base.isTerm() && inst.isTerm());

    Term* varHeadTerm = base.term();
    Term* matchableTerm = inst.term();

    ASS(varHeadTerm->hasVarHead());

    unsigned arityDiff = matchableTerm->arity() - varHeadTerm->arity();
    Prefix pref = Prefix(matchableTerm->functor(), matchableTerm->nthArgument(arityDiff), arityDiff);
    return pref;
  }

private:
  typedef DHMap<unsigned,TermList,IdentityHash> BindingMap;
  struct MapBinder
  {
    bool bind(unsigned var, Prefix pref)
    {
      //dummy does nothing at the moment.
     return false;
    }

    bool bind(unsigned var, TermList term)
    {
      TermList* aux;
      return _map.getValuePtr(var,aux,term) || *aux==term;
    }
    void specVar(unsigned var, TermList term)
    { ASSERTION_VIOLATION; }
    void reset() { _map.reset(); }
  private:
    BindingMap _map;
  };


};

/**
 * Class of objects that iterate over matches between two literals that
 * may share variables (therefore it has to perform occurs check).
 */
class OCMatchIterator
{
public:
  void init(Literal* base, Literal* inst, bool complementary);

  bool tryNextMatch();

  TermList apply(unsigned var);
  TermList applyHigherOrder(Term* varHeadTerm);
  TermList apply(TermList t);
  Literal* apply(Literal* lit);

private:

  void reset();

  bool tryDirectMatch();
  bool tryReversedMatch();

  enum OCStatus {
    ENQUEUED,
    TRAVERSING,
    CHECKED
  };
  bool occursCheck();


  bool bind(unsigned var, Prefix pref)
  {
    //dummy does nothing at the moment.
   return false;
  }

  bool bind(unsigned var, TermList term)
  {
    TermList* binding;

    if(_bindings.getValuePtr(var,binding,term)) {
      _bound.push(var);
      return true;
    }
    return *binding==term;
  }
  void specVar(unsigned var, TermList term)
  { ASSERTION_VIOLATION; }


  typedef DHMap<unsigned,TermList> BindingMap;
  typedef Stack<unsigned> BoundStack;

  BindingMap _bindings;
  BoundStack _bound;
  bool _finished;
  bool _firstMatchDone;
  Literal* _base;
  Literal* _inst;

  friend class MatchingUtils;
};

class Matcher
: public Backtrackable
{
public:
  Matcher() : _binder(*this) {}

  MatchIterator matches(Literal* base, Literal* instance, bool complementary);

private:
  class CommutativeMatchIterator;

  struct MatchContext;

  bool matchArgs(Literal* base, Literal* instance);

  bool matchReversedArgs(Literal* base, Literal* instance);

  typedef DHMap<unsigned,TermList> BindingMap;
  struct MapBinder
  {
    MapBinder(Matcher& parent) : _parent(parent) {}

    bool bind(unsigned var, Prefix pref)
    {
      //dummy does nothing at the moment.
     return false;
    }

    bool bind(unsigned var, TermList term)
    {
      TermList* aux;
      if(_map.getValuePtr(var,aux,term)) {
        if(_parent.bdIsRecording()) {
          _parent.bdAdd(new BindingBacktrackObject(this,var));
        }
        return true;
      } else {
        return *aux==term;
      }
    }
    void specVar(unsigned var, TermList term)
    { ASSERTION_VIOLATION; }
  private:
    BindingMap _map;
    Matcher& _parent;

    class BindingBacktrackObject
    : public BacktrackObject
    {
    public:
      BindingBacktrackObject(MapBinder* bnd, unsigned var)
      :_map(&bnd->_map), _var(var) {}
      void backtrack()
      { ALWAYS(_map->remove(_var)); }

      CLASS_NAME(Matcher::MapBinder::BindingBacktrackObject);
      USE_ALLOCATOR(BindingBacktrackObject);
    private:
      BindingMap* _map;
      unsigned _var;
    };
  };

  MapBinder _binder;
};

/**
 * Matches two terms, using @b binder to store and check bindings
 * of base variables. @b binder must be a functor with parameters
 * (unsigned var, TermList term), that in case variable @b var is
 * unbound, binds it to @b term and returns true, if @b var is
 * bound, returns true iff it is bound to @b term.
 */
template<class Binder>
bool MatchingUtils::matchArgs(Term* base, Term* instance, Binder& binder)
{
  CALL("MatchingUtils::matchArgs");
  ASS_EQ(base->functor(),instance->functor());
  //weight is not defined for higher-order functor symbols yet. AYB
  if(base->shared() && instance->shared() && !base->hoVars() && !instance->hoVars()) {
    if(base->weight() > instance->weight() || !instance->couldArgsBeInstanceOf(base)) {
      return false;
    }
  }
  ASS_G(base->arity(),0);

  TermList* bt=base->args();
  TermList* it=instance->args();

  static Stack<TermList*> subterms(32);
  subterms.reset();

  for (;;) {
    if (!bt->next()->isEmpty()) {
      subterms.push(it->next());
      subterms.push(bt->next());
    }
    if(bt->isSpecialVar()) {
      binder.specVar(bt->var(), *it);
    } else if(it->isSpecialVar()) {
      binder.specVar(it->var(), *bt);
    } else if(bt->isTerm()) {
      if(!it->isTerm()) {
        return false;
      }
      Term* s = bt->term();
      Term* t = it->term();
      bool matchableVarHead = hasMatchableVarHead(*bt, *it);
      if(s->functor()!=t->functor() && !matchableVarHead) {
        return false;
      }
      if(matchableVarHead){
        Prefix pref = getPrefix(*bt, *it);
        if(!binder.bind(s->functor(),pref)) {
          return false;
        }
      } else {
        //both terms shared 
        if(s->shared() && t->shared()) {
          if(s->ground() && *bt!=*it) {
            return false;
          }
          if(!s->hoVars() && !t->hoVars() && s->weight() > t->weight()) {
            return false;
          }
        }
      }
      if(s->arity() > 0) {
        bt = s->args();
        it = t->args();
        continue;
      }
    } else {
      ASS(bt->isOrdinaryVar());
      if(!binder.bind(bt->var(), *it)) {
        return false;
      }
    }
    if(subterms.isEmpty()) {
      return true;
    }
    bt = subterms.pop();
    it = subterms.pop();
  }
}

};

#endif /* __Matcher__ */
