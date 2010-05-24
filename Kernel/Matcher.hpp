/**
 * @file Matcher.hpp
 * Defines class Matcher.
 */


#ifndef __Matcher__
#define __Matcher__

#include "Forwards.hpp"

#include "Lib/BacktrackData.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Hash.hpp"
#include "Lib/Stack.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Term.hpp"
#include "TermIterators.hpp"

namespace Kernel {

using namespace Lib;

class MatchingUtils
{
public:

  static bool isVariant(Literal* l1, Literal* l2, bool complementary=false)
  {
    if(!Literal::headersMatch(l1,l2,complementary)) {
      return false;
    }
    if(!complementary && l1==l2) {
      return true;
    }
    if(l1->commutative()) {
      return haveVariantArgs(l1,l2) || haveReversedVariantArgs(l1,l2);
    } else {
      return haveVariantArgs(l1,l2);
    }
  }

  static bool haveReversedVariantArgs(Term* l1, Term* l2)
  {
    ASS_EQ(l1->arity(), 2);
    ASS_EQ(l2->arity(), 2);

    static DHMap<unsigned,unsigned,IdentityHash> leftToRight;
    static DHMap<unsigned,unsigned,IdentityHash> rightToLeft;
    leftToRight.reset();
    rightToLeft.reset();

    VirtualIterator<pair<TermList, TermList> > dsit=pvi( getConcatenatedIterator(
	    vi( new DisagreementSetIterator(*l1->nthArgument(0),*l2->nthArgument(1)) ),
	    vi( new DisagreementSetIterator(*l1->nthArgument(1),*l2->nthArgument(0)) )) );
    while(dsit.hasNext()) {
      pair<TermList,TermList> dp=dsit.next(); //disagreement pair
      if(!dp.first.isVar() || !dp.second.isVar()) {
	return false;
      }
      unsigned left=dp.first.var();
      unsigned right=dp.second.var();
      if(right!=leftToRight.findOrInsert(left,right)) {
	return false;
      }
      if(left!=rightToLeft.findOrInsert(right,left)) {
	return false;
      }
    }
    if(leftToRight.size()!=rightToLeft.size()) {
      return false;
    }

    return true;
  }

  static bool haveVariantArgs(Term* l1, Term* l2)
  {
    ASS_EQ(l1->arity(), l2->arity());

    if(l1==l2) {
      return true;
    }
    static DHMap<unsigned,unsigned,IdentityHash> leftToRight;
    static DHMap<unsigned,unsigned,IdentityHash> rightToLeft;
    leftToRight.reset();
    rightToLeft.reset();

    DisagreementSetIterator dsit(l1,l2);
    while(dsit.hasNext()) {
      pair<TermList,TermList> dp=dsit.next(); //disagreement pair
      if(!dp.first.isVar() || !dp.second.isVar()) {
	return false;
      }
      unsigned left=dp.first.var();
      unsigned right=dp.second.var();
      if(right!=leftToRight.findOrInsert(left,right)) {
	return false;
      }
      if(left!=rightToLeft.findOrInsert(right,left)) {
	return false;
      }
    }
    if(leftToRight.size()!=rightToLeft.size()) {
      return false;
    }

    return true;
  }

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

  static bool matchReversedArgs(Literal* base, Literal* instance)
  {
    CALL("MatchingUtils::match");
    ASS_EQ(base->arity(), 2);
    ASS_EQ(instance->arity(), 2);

    static MapBinder binder;
    binder.reset();

    return matchTerms(*base->nthArgument(0), *instance->nthArgument(1), binder) &&
      matchTerms(*base->nthArgument(1), *instance->nthArgument(0), binder);
  }

  static bool matchArgs(Term* base, Term* instance)
  {
    static MapBinder binder;
    binder.reset();

    return matchArgs(base, instance, binder);
  }

  static bool matchTerms(TermList base, TermList instance)
  {
    CALL("MatchingUtils::matchTerms/2");

    if(base.isTerm()) {
      if(!instance.isTerm()) {
	return false;
      }

      Term* bt=base.term();
      Term* it=instance.term();
      if(bt->functor()!=it->functor()) {
	return false;
      }
      if(bt->shared() && it->shared()) {
        if(bt->ground()) {
          return bt==it;
        }
        if(bt->weight() > it->weight()) {
          return false;
        }
      }
      ASS_G(base.term()->arity(),0);
      return matchArgs(bt, it);
    } else {
      return true;
    }
  }

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

      CLASS_NAME("Matcher::BindingBacktrackObject");
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
  if(base->shared() && instance->shared()) {
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
