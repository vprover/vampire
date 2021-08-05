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

#include "Term.hpp"
#include "TermIterators.hpp"
#include "SortHelper.hpp"

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
   * Matches two literals,
   * using @b binder to store and check bindings of base variables.
   *
   * @b binder must have the following functions:
   * - void reset()
   *   resets the bindings,
   * - bool bind(unsigned var, TermList term)
   *   if variable @b var is unbound, binds it to @b term and returns true,
   *   otherwise returns true iff it is bound to @b term,
   * - void specVar(unsigned var, TermList term)
   *   called to bind special variable @b var to @b term.
   *
   * The @b binder will be reset before the first time it is used.
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
      ASS_EQ(base->arity(), 2);
      if(matchArgs(base, instance, binder)) {
        return true;
      }
      binder.reset();
      return matchReversedArgs(base, instance, binder);
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

  template<class Binder>
  static bool matchReversedArgs(Literal* base, Literal* instance, Binder& binder);

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

private:
  typedef DHMap<unsigned,TermList,IdentityHash> BindingMap;
  struct MapBinder
  {
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
 * Matches two binary literals like MatchingUtils::matchArgs,
 * but with the arguments of one literal swapped.
 */
template<class Binder>
bool MatchingUtils::matchReversedArgs(Literal* base, Literal* instance, Binder& binder)
{
  CALL("MatchingUtils::matchReversedArgs/3");
  ASS_EQ(base->functor(), instance->functor());
  ASS_EQ(base->arity(), 2);
  ASS_EQ(instance->arity(), 2);

  if (base->isTwoVarEquality()) {
    if (!matchTerms(base->twoVarEqSort(), SortHelper::getEqualityArgumentSort(instance), binder)) {
      return false;
    }
  }
  return matchTerms(*base->nthArgument(0), *instance->nthArgument(1), binder)
    &&   matchTerms(*base->nthArgument(1), *instance->nthArgument(0), binder);
}

/**
 * Matches two terms, using @b binder to store and check bindings
 * of base variables.
 *
 * See MatchingUtils::match for a description of @b binder.
 */
template<class Binder>
bool MatchingUtils::matchArgs(Term* base, Term* instance, Binder& binder)
{
  CALL("MatchingUtils::matchArgs");
  ASS_EQ(base->functor(),instance->functor());
  if(base->shared() && instance->shared()) {
    if(base->weight() > instance->weight()) {
      return false;
    }
  }
  // Note: while this function only cares about the term structure,
  // for two-variable equalities we need to get the sort of the arguments from the Literal object.
  if(base->isLiteral() && static_cast<Literal*>(base)->isTwoVarEquality()){
    Literal* l1 = static_cast<Literal*>(base);
    Literal* l2 = static_cast<Literal*>(instance);
    if(!matchTerms(l1->twoVarEqSort(), SortHelper::getEqualityArgumentSort(l2), binder)){
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
      if(s->functor()!=t->functor()) {
	return false;
      }
      if(bt->term()->shared() && it->term()->shared()) {
	if(bt->term()->ground() && *bt!=*it) {
	  return false;
	}
	if(s->weight() > t->weight()) {
	  return false;
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
