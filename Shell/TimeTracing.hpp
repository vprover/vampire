/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#ifndef __TimeTracing__
#define __TimeTracing__

#include "Lib/Stack.hpp"
#include "Lib/Option.hpp"
#include "Kernel/Ordering.hpp"
#include "Debug/Assertion.hpp"
#include "Kernel/Term.hpp"
#include <chrono>
#include "Lib/MacroUtils.hpp"

namespace Shell {

#define TIME_TRACE(name)                                                                            \
  Shell::TimeTrace::ScopedTimer CONCAT_IDENTS(__time_trace_, __LINE__) (name);

#define TIME_TRACE_EXPR(name, ...)                                                                  \
  [&](){ TIME_TRACE(name); return __VA_ARGS__; }()

class TimeTrace 
{
  using Clock = std::chrono::high_resolution_clock;
  using Duration = typename Clock::duration;
  using TimePoint = typename Clock::time_point;

  TimeTrace(TimeTrace     &&) = delete;
  TimeTrace(TimeTrace const&) = delete;

  struct Node {
    CLASS_NAME(Node)
    USE_ALLOCATOR(Node)
    const char* name;
    Lib::Stack<unique_ptr<Node>> children;
    Lib::Stack<Duration> measurements;
    Node(const char* name) : name(name), children(), measurements() {}
    void print(std::ostream& out, unsigned indent, Lib::Option<Node const&> parent);
    Duration totalDuration() const;
  };

public:
  TimeTrace();

  class ScopedTimer {
    TimeTrace& _trace;
#if VDEBUG
    TimePoint _start;
    const char* _name;
#endif
  public:
    ScopedTimer(const char* name);
    ScopedTimer(TimeTrace& trace, const char* name);
    ~ScopedTimer();
  };

  void print(std::ostream& out);
private:

  Node _root;
  Lib::Stack<std::tuple<Node*, TimePoint>> _stack;
};


template<class Iter>
class TimeTraceIter
{
  const char* _name;
  Iter _iter;
public:
  TimeTraceIter(const char* name, Iter iter) 
    : _name(name)
    , _iter(std::move(iter)) 
  {}

  DECL_ELEMENT_TYPE(ELEMENT_TYPE(Iter));

  OWN_ELEMENT_TYPE next() { TIME_TRACE(_name); return _iter.next(); }
  bool hasNext() { TIME_TRACE(_name); return _iter.hasNext(); }

  bool knowsSize() const 
  { return _iter.knowsSize(); }

  size_t size() const
  { return _iter.size(); }

};

template<class Iter>
auto timeTraced(const char* name, Iter iter) 
{ return TimeTraceIter<Iter>(name, std::move(iter)); }


template<class Ord>
class TimeTraceOrdering : public Kernel::Ordering
{
  const char* _nameLit;
  const char* _nameTerm;
  Ord _ord;
public:
  CLASS_NAME(TimeTraceOrdering);
  USE_ALLOCATOR(TimeTraceOrdering);

  TimeTraceOrdering(const char* nameLit, const char* nameTerm, Ord ord)
  : _nameLit(nameLit)
  , _nameTerm(nameTerm)
  , _ord(std::move(ord))
  { }

  ~TimeTraceOrdering() override {  }

  Result compare(Kernel::Literal* l1, Kernel::Literal* l2) const final override
  { TIME_TRACE(_nameLit); return _ord.compare(l1,l2); }

  Result compare(Kernel::TermList l1, Kernel::TermList l2) const final override
  { TIME_TRACE(_nameTerm); return _ord.compare(l1,l2); }

  // TODO shouldn't this be a function of PrecedenceOrdering?
  Kernel::Comparison compareFunctors(unsigned fun1, unsigned fun2) const final override 
  { ASSERTION_VIOLATION }

  void show(ostream& out) const final override
  { _ord.show(out); }

  Ord      & inner()       { return _ord; }
  Ord const& inner() const { return _ord; }
};

} // namespace Shell

#endif // __TimeTracing__
