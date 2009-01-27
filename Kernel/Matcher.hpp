/**
 * @file Matcher.hpp
 * Defines class Matcher.
 */


#ifndef __Matcher__
#define __Matcher__

#include "../Forwards.hpp"

#include "../Lib/BacktrackData.hpp"
#include "../Lib/DHMap.hpp"
#include "../Lib/Hash.hpp"
#include "../Lib/VirtualIterator.hpp"

namespace Kernel {

using namespace Lib;

class MatchingUtils
{
public:
  static bool match(Literal* base, Literal* instance, bool complementary)
  {
    CALL("MatchingUtils::match");

    if(!Literal::headersMatch(base,instance,complementary)) {
      return false;
    }
    static MapBinder binder;
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

  template<class Binder>
  static bool matchTerms(TermList base, TermList instance, Binder& binder)
  {
    CALL("MatchingUtils::matchTerms");

    if(base.isTerm()) {
      if(!instance.isTerm()) {
	return false;
      }
      return matchArgs(base.term(), instance.term(), binder);
    } else {
      ASS(base.isOrdinaryVar());
      return binder(base.var(), instance);
    }
  }

  template<class Binder>
  static bool matchArgs(Term* base, Term* instance, Binder& binder);

private:
  typedef DHMap<unsigned,TermList,IdentityHash<unsigned> > BindingMap;
  struct MapBinder
  {
    bool operator()(unsigned var, TermList term)
    {
      TermList* aux;
      return _map.getValuePtr(var,aux,term) || *aux==term;
    }
    void reset() { _map.reset(); }
  private:
    BindingMap _map;
  };

};


class Matcher
: Backtrackable
{
public:
  Matcher() : _binder(*this) {}

  MatchIterator matches(Literal* base, Literal* instance,
	  bool complementary)
  {
    if(!Literal::headersMatch(base, instance, complementary)) {
      return MatchIterator::getEmpty();
    }
    if( !base->commutative() ) {
      return pvi( getContextualIterator(getSingletonIterator(this),
	      MatchContext(base, instance)) );
    }
    return vi( new CommutativeMatchIterator(this, base, instance) );

  }

private:
  class CommutativeMatchIterator
  : public IteratorCore<Matcher*>
  {
  public:
    CommutativeMatchIterator(Matcher* matcher, Literal* base, Literal* instance)
    : _matcher(matcher), _base(base), _instance(instance),
    _state(FIRST), _used(true)
    {
      ASS(_base->commutative());
      ASS_EQ(_base->arity(), 2);
    }
    ~CommutativeMatchIterator()
    {
      if(_state!=FINISHED) {
	backtrack();
      }
      ASS(_bdata.isEmpty());
    }
    bool hasNext()
    {
      CALL("Matcher::CommutativeMatchIterator::hasNext");

      if(_state==FINISHED) {
        return false;
      }
      if(!_used) {
        return true;
      }
      _used=false;

      if(_state!=FIRST) {
        //undo the previous match
	backtrack();
      }
      _matcher->bdRecord(_bdata);

      switch(_state) {
      case NEXT_STRAIGHT:
	if(_matcher->matchArgs(_base,_instance)) {
	  _state=NEXT_REVERSED;
	  break;
	}
	//no break here intentionally
      case NEXT_REVERSED:
	if(_matcher->matchReversedArgs(_base,_instance)) {
	  _state=NEXT_CLEANUP;
	  break;
	}
      //no break here intentionally
      case NEXT_CLEANUP:
        //undo the previous match
	backtrack();

	_state=FINISHED;
#if VDEBUG
	break;
      default:
	ASSERTION_VIOLATION;
#endif
      }

      ASS(_state!=FINISHED || _bdata.isEmpty());
      return _state!=FINISHED;
    }
    Matcher* next()
    {
      _used=true;
      return _matcher;
    }
  private:
    void backtrack()
    {
      ASS_EQ(&_bdata,&_matcher->bdGet());
      _matcher->bdDone();
      _bdata.backtrack();
    }

    enum State {
      FIRST=0,
      NEXT_STRAIGHT=0,
      NEXT_REVERSED=1,
      NEXT_CLEANUP=2,
      FINISHED=3
    };
    Matcher* _matcher;
    Literal* _base;
    Literal* _instance;
    BacktrackData _bdata;

    State _state;
    /**
     * true if the current substitution have already been
     * retrieved by the next() method, or if there isn't
     * any (hasNext() hasn't been called yet)
     */
    bool _used;
  };

  struct MatchContext
  {
    MatchContext(Literal* base, Literal* instance)
    : _base(base), _instance(instance) {}
    bool enter(Matcher* matcher)
    {
      CALL("Matcher::MatchContext::enter");

      matcher->bdRecord(_bdata);
      bool res=matcher->matchArgs(_base, _instance);
      if(!res) {
	matcher->bdDone();
        ASS(_bdata.isEmpty());
      }
      return res;
    }
    void leave(Matcher* matcher)
    {
      matcher->bdDone();
      _bdata.backtrack();
    }
  private:
    Literal* _base;
    Literal* _instance;
    BacktrackData _bdata;
  };

  bool matchArgs(Literal* base, Literal* instance)
  {
    CALL("Matcher::matchArgs");

    BacktrackData localBD;

    bdRecord(localBD);
    bool res=MatchingUtils::matchArgs(base,instance, _binder);
    bdDone();

    if(res) {
      if(bdIsRecording()) {
        bdCommit(localBD);
      }
      localBD.drop();
    } else {
      localBD.backtrack();
    }
    return res;
  }

  bool matchReversedArgs(Literal* base, Literal* instance)
  {
    CALL("Matcher::matchReversedArgs");
    ASS(base->commutative());

    BacktrackData localBD;

    bdRecord(localBD);
    bool res=MatchingUtils::matchTerms(*base->nthArgument(0), *instance->nthArgument(1), _binder);
    if(res) {
      res=MatchingUtils::matchTerms(*base->nthArgument(1), *instance->nthArgument(0), _binder);
    }
    bdDone();

    if(res) {
      if(bdIsRecording()) {
        bdCommit(localBD);
      }
      localBD.drop();
    } else {
      localBD.backtrack();
    }
    return res;
  }

  typedef DHMap<unsigned,TermList,IdentityHash<unsigned> > BindingMap;
  struct MapBinder
  {
    MapBinder(Matcher& parent) : _parent(parent) {}
    bool operator()(unsigned var, TermList term)
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
  ASS(base->shared());
  ASS(instance->shared());
  if(base==instance && base->ground()) {
    return true;
  }

  TermList* bt=base->args();
  TermList* it=instance->args();

  static Stack<TermList*> subterms(32);
  subterms.reset();

  for (;;) {
    if (!bt->next()->isEmpty()) {
      subterms.push(it->next());
      subterms.push(bt->next());
    }

    if(bt->isTerm()) {
      if(*bt==*it && bt->term()->ground()) {
      } else if (TermList::sameTopFunctor(bt,it)) {
	Term* s = bt->term();
	Term* t = it->term();
	if(s->arity() > 0) {
	  bt = s->args();
	  it = t->args();
	  continue;
	}
      } else {
	return false;
      }
    } else {
      ASS(bt->isOrdinaryVar());
      if(!binder(bt->var(), *it)) {
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
