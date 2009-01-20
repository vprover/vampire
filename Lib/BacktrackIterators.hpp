/**
 * @file BacktrackIterators.hpp
 * Defines class BacktrackIterators.
 */


#ifndef __BacktrackIterators__
#define __BacktrackIterators__

#include "DArray.hpp"
#include "Stack.hpp"
#include "VirtualIterator.hpp"
#include "Metaiterators.hpp"

namespace Lib {

/**
 * Iterator on states, which goes over all possible
 * combinations of choices (which are enumerated by Fn).
 *
 * ChoiceArr is an array-like class containing elements
 * that correspont to choice points. Let ChoicePoint
 * denote type of a single choice point.
 *
 * Fn is a class with static method succ enumerating all
 * possible successive states at given choice point:
 *
 * static VirtualIterator<State> succ(State curr, ChoicePoint cp)
 */
template<typename State, typename ChoiceArr, class Fn>
class BacktrackingIterator
: public IteratorCore<State>
{
public:
  BacktrackingIterator(State initState, ChoiceArr& choices, size_t chLen)
  : _fin(false), _used(true), _choices(choices), _chLen(chLen),
  _chits(32), _states(32)
  {
    ASS(_chLen>0);
    _states.push(initState);
  }
  bool hasNext()
  {
    if(_fin) {
      return false;
    }
    if(!_used) {
      return true;
    }
    if(depth()) {
      ASS_EQ(depth(), _chLen);
      _states.pop();
    } else {
      _chits.push(Fn::succ(_states.top(), _choices[depth()]));
    }
    for(;;) {
      while( _chits.isNonEmpty() && !_chits.top().hasNext() ) {
	_chits.pop();
	_states.pop();
      }
      if(_chits.isNonEmpty()) {
	_states.push(_chits.top().next());
      } else {
	_fin=true;
	return false;
      }
      if(depth()==_chLen) {
	break;
      }
      _chits.push(Fn::succ(_states.top(), _choices[depth()]));
    }
    _used=false;
    return true;
  }
  State next()
  {
    ASS(!_used);
    ASS(!_fin);
    _used=true;
    return _states.top();
  }
private:
  size_t depth() { return _chits.length(); }

  bool _fin;
  bool _used;
  State _initState;
  ChoiceArr& _choices;
  size_t _chLen;
  Stack<VirtualIterator<State> > _chits; //choice iterators
  Stack<State> _states;
};


template<class Fn, typename State, typename ChoiceArr>
VirtualIterator<State> getBacktrackingIterator(State initState,
	ChoiceArr& choices, size_t chLen)
{
  if(chLen==0) {
    return getSingletonIterator(initState);
  }
  return VirtualIterator<State>(new BacktrackingIterator<Fn,State,ChoiceArr>
	  (initState, choices, chLen));
}

template<class Fn, typename State, typename ChoicePoint>
class FnForIterable
{
  class FnFunctor
  {
  public:
    FnFunctor(State s) : _state(s) {}

    VirtualIterator<State> operator() (ChoicePoint cp)
    { return Fn::succ(_state, cp); }
  private:
    State _state;
  };
public:
  template<class ChPntIterable>
  static VirtualIterator<State> succ(State curr, ChPntIterable cpitb) //cpitb=Choice Point ITeraBle
  {
    VirtualIterator<ChoicePoint> cpit=getContentIterator(cpitb);
    return getFlattenedIterator( getMappingIterator<State>(cpit, FnFunctor(curr)) );
  }
};

};

#endif /* __BacktrackIterators__ */
