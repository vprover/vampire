/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Debug/Assertion.hpp"
#include "Lib/Deque.hpp"
#include "Test/UnitTesting.hpp"

TEST_FUN(push_front_pop_back_expand)
{
  Lib::Deque<int> *a_deque = new Lib::Deque<int>(2);
  a_deque->push_front(0);
  ASS_EQ(a_deque->pop_back(), 0);
  // push front until capacity expand
  a_deque->push_front(1);
  a_deque->push_front(2);
  // push back until capacity expand
  a_deque->push_back(3);
  a_deque->push_back(4);
  ASS_EQ(a_deque->size(), 4);
}

TEST_FUN(size_reset_desctructor)
{
  Lib::Deque<int> *a_deque = new Lib::Deque<int>();
  a_deque->push_front(1);
  a_deque->reset();
  ASS_EQ(a_deque->size(), 0);
  a_deque->push_front(1);
  // gcov sometimes misses implicitly called desctructor
  a_deque->~Deque();
}
