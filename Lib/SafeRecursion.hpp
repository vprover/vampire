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
 * @file SafeRecursion.hpp
 * Defines class SafeRecursion.
 */

#ifndef __SafeRecursion__
#define __SafeRecursion__

#include <algorithm>

#include "Forwards.hpp"

#include "Stack.hpp"

namespace Lib {

/**
 * Performs a stack-safe traversal of a tree-like structure.
 *
 * Class takes Worker class as an argument. The worker class should have the following functions:
 *
 * template<class ChildCallback>
 * void pre(Arg obj, ChildCallback fn);
 *
 * Res post(Arg obj, size_t childCnt, Res* childRes);
 *
 * The ChildCallback fn is a functor that is to be called with children of obj.
 *
 * The @c post function is allowed to modify the childResArray.
 *
 */
template<typename Arg, typename Res, class Worker>
struct SafeRecursion
{
  SafeRecursion(Worker w) : w(w) {}

  Res operator()(Arg obj0)
  {
    ChildCallback callback(*this);

    children.push(obj0);

    for(;;) {

      {
	Arg obj = children.pop();

	size_t prevChildrenSz = children.size();
	w.pre(obj, callback);
	size_t chCnt = children.size() - prevChildrenSz;

	waiting.push(obj);
	childrenCounts.push(chCnt);
	childrenRemaining.push(chCnt);
	ASS_EQ(waiting.size(),childrenCounts.size());
	ASS_EQ(waiting.size(),childrenRemaining.size());
      }

      while(childrenRemaining.top()==0) {
	size_t childCnt = childrenCounts.top();
	//here we put the children results in the right order
	std::reverse(results.end()-childCnt, results.end());

	//call the result processing
	Res res = w.post(waiting.top(), childCnt, results.end()-childCnt);

	//remove the results which we have just consumed
	results.truncate(results.size()-childCnt);
	//and add the new result instead
	results.push(res);

	waiting.pop();
	childrenCounts.pop();
	childrenRemaining.pop();

	if(waiting.isEmpty()) {
	  ASS(children.isEmpty());
	  ASS(childrenCounts.isEmpty());
	  ASS(childrenRemaining.isEmpty());
	  ASS_EQ(results.size(),1);
	  return results.pop();
	}

	ASS_NEQ(childrenRemaining.top(), 0);
	childrenRemaining.top()--;
      }
    }
  }
private:
  struct ChildCallback
  {
    ChildCallback(SafeRecursion& parent) : parent(parent) {}
    void operator()(Arg child) {
      parent.children.push(child);
    }
    SafeRecursion& parent;
  };

  Worker w;
  Stack<Arg> children;
  Stack<Arg> waiting;
  Stack<size_t> childrenCounts;
  Stack<size_t> childrenRemaining;
  Stack<Res> results;
};

}

#endif // __SafeRecursion__
