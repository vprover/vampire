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
 * @file BacktrackIterators.hpp
 * Defines class BacktrackIterators.
 *
 * These iterators are not being used in the current code, so they
 * are not well documented and may be buggy.
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
	ALWAYS(_chits.top().hasNext());
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
  Stack<std::invoke_result_t<Fn, State>> _chits; //choice iterators
  Stack<State> _states;
  Fn _functor;
};

template<typename State, typename ChoiceArr, class Fn>
VirtualIterator<State> getBacktrackingIterator(State initState,
	ChoiceArr choices, Fn functor)
{
  size_t chLen=choices.size();
  if(chLen==0) {
    return pvi( getSingletonIterator(initState) );
  }
  return VirtualIterator<State>(new BacktrackingIterator<State,ChoiceArr,Fn>
	  (initState, choices, chLen, functor));
}

///@}

};

#endif /* __BacktrackIterators__ */
