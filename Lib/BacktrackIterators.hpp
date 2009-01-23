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

///@addtogroup Iterators
///@{

/**
 * Iterator on states, which goes over all possible
 * combinations of choices (which are enumerated by Fn).
 *
 * ChoiceArr is an array-like class containing elements
 * that correspont to choice points. Let ChoicePoint
 * denote type of a single choice point.
 *
 * Fn is a functor which enumerates all possible successive
 * states at given choice point:
 *
 * VirtualIterator<State> (*function)(State curr, ChoicePoint cp)
 */
template<typename State, typename ChoiceArr, class Fn>
class BacktrackingIterator
: public IteratorCore<State>
{
public:
  BacktrackingIterator(State initState, ChoiceArr choices, size_t chLen, Fn functor)
  : _fin(false), _used(true), _choices(choices), _chLen(chLen),
  _chits(32), _states(32), _functor(functor)
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
      _chits.push(_functor(_states.top(), _choices[depth()]));
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
      _chits.push(_functor(_states.top(), _choices[depth()]));
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
  ChoiceArr _choices;
  size_t _chLen;
  Stack<VirtualIterator<State> > _chits; //choice iterators
  Stack<State> _states;
  Fn _functor;
};

template<typename State, typename ChoiceArr, class Fn>
VirtualIterator<State> getBacktrackingIterator(State initState,
	ChoiceArr choices, Fn functor)
{
  size_t chLen=choices.size();
  if(chLen==0) {
    return getSingletonIterator(initState);
  }
  return VirtualIterator<State>(new BacktrackingIterator<State,ChoiceArr,Fn>
	  (initState, choices, chLen, functor));
}

template<typename State, class Fn>
class BtrFnForIterable
{
  class FnMapper
  {
  public:
    DECL_RETURN_TYPE(VirtualIterator<State>);
    FnMapper(State s, Fn functor) : _state(s), _functor(functor) {}

    template<typename ChoicePoint>
    OWN_RETURN_TYPE operator() (ChoicePoint cp)
    { return _functor(_state, cp); }
  private:
    State _state;
    Fn _functor;
  };

public:
  BtrFnForIterable(Fn functor) : _functor(functor) {}

  template<class ChPntIterable>
  VirtualIterator<State> operator() (State curr, ChPntIterable cPItb) //cPItb=Choice Point ITeraBle
  {
    return getFlattenedIterator(
	    getMappingIterator(
		    getContentIterator(cPItb),
		    FnMapper(curr, _functor)) );
  }
private:
  Fn _functor;
};

template<typename State, class Fn>
BtrFnForIterable<State, Fn> getBacktrackFnForIterableChoicePoint(Fn functor)
{
  return BtrFnForIterable<State,Fn>(functor);
}


///@}

};

#endif /* __BacktrackIterators__ */
