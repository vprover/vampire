/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#if VTIME_PROFILING

#include "Debug/TimeProfiling.hpp"
#include <iomanip>
#include <cstring>
#include "Shell/Options.hpp"
#include "Lib/Environment.hpp"

namespace Shell {

using namespace std;
using namespace Lib;

TimeTrace::TimeTrace()
  : _root("[root]")
  , _stack({ {&_root, Clock::now(), }, })
  , _enabled(false)
{  }

TimeTrace::ScopedTimer::ScopedTimer(const char* name)
  : ScopedTimer(TimeTrace::instance(), name)
{ }

TimeTrace::ScopedTimer::ScopedTimer(TimeTrace& trace, const char* name)
  : _trace(trace)
  , _active(trace._enabled.load(std::memory_order_relaxed))
#if VDEBUG
  , _start()
  , _name(name)
#endif
{
  if (_active) {
    auto& children = std::get<0>(trace._stack.back())->children;
    Node* node = nullptr;
    for (auto& c : children) {
      if (c->name == name) {
        node = &*c;
        break;
      }
    }
    if (!node) {
      children.push_back(std::make_unique<Node>(name));
      node = &*children.back();
    }
    auto start = Clock::now();
#if VDEBUG
    _start = start;
#endif

    _trace._stack.push_back(std::make_pair(node, start));
  }
}

TimeTrace TimeTrace::_instance;

void TimeTrace::setEnabled(bool v)
{ _enabled.store(v, std::memory_order_relaxed); }

TimeTrace::ScopedTimer::~ScopedTimer()
{
  // tracing was off when we were constructed, so there is nothing on the stack for us
  if (!_active)
    return;
  // tracing has been turned off since: the trace is frozen so that someone else can
  // print it (see setEnabled). Leave it strictly alone -- we are about to exit anyway.
  if (!_trace._enabled.load(std::memory_order_relaxed))
    return;

  auto now = Clock::now();
  auto cur = _trace._stack.back();
  _trace._stack.pop_back();
  auto node = get<0>(cur);
  auto start = get<1>(cur);
  node->measurements.add(now  - start);
  ASS_EQ(node->name, _name);
  ASS(start == _start);
}


TimeTrace::ScopedChangeRoot::ScopedChangeRoot()
  : ScopedChangeRoot(TimeTrace::instance())
{ }

TimeTrace::ScopedChangeRoot::ScopedChangeRoot(TimeTrace& trace)
  : _trace(trace)
{
  if (_trace._enabled.load(std::memory_order_relaxed)) {
    _trace._tmpRoots.push_back(get<0>(trace._stack.back()));
  }
}

TimeTrace::ScopedChangeRoot::~ScopedChangeRoot()
{
  // see ~ScopedTimer: never pop what we did not push, and never touch a frozen trace
  if (_trace._enabled.load(std::memory_order_relaxed) && !_trace._tmpRoots.empty()) {
    _trace._tmpRoots.pop_back();
  }
}

TimeTrace::Duration TimeTrace::Node::totalDuration() const
{ return measurements.sum(); }
  
std::ostream& operator<<(std::ostream& out, TimeTrace::Duration const& self)
{ 
  using namespace std::chrono;
  if(self >= 10s) {
    return out << duration_cast<seconds>(self).count() << " s"; 
  } else if (self >= 10ms) {
    return out << duration_cast<milliseconds>(self).count() << " ms"; 
  } else if (self >= 10us) {
    return out << duration_cast<microseconds>(self).count() << " μs"; 
  } else {
    return out << duration_cast<nanoseconds>(self).count() << " ns"; 
  }
// << duration_cast<microseconds>(total / cnt).count() << " μs"
}

struct TimeTrace::Node::NodeFormatOpts {
  // std::vector, not Lib::Stack: printing runs on the timer thread, see Node
  std::vector<const char*>& indent;
  Lib::Option<Duration> parentDuration;
  bool last;
  bool align;
  Lib::Option<unsigned> nameWidth;

  NodeFormatOpts child(Node& parent) 
  { return { .indent = this->indent, 
             .parentDuration = some(parent.totalDuration()), 
             .last = false, 
             .align = this->align,
             .nameWidth = align
               ? iterTraits(arrayIter(parent.children))
                   .map([](auto& c) { return unsigned(strlen(c->name)); })
                   .max()
               : none<unsigned>(),
               }; }

  static NodeFormatOpts root(decltype(indent) indent) 
  { return { .indent = indent, 
             .parentDuration = Option<Duration>(), 
             .last = true, 
             .align = false,
             .nameWidth = none<unsigned>(),
           }; }
};

static constexpr const char* indentBeforeLast = "  │  ";
static constexpr const char* internalChild    = "  ├──";
static constexpr const char* lastChild        = "  └──";
static constexpr const char* indentAfterLast  = "     ";


struct MaybeSetw {
  bool enabled;
  int width;
  friend std::ostream& operator<<(std::ostream& out, MaybeSetw const& self)
  { 
    if (self.enabled) return out << setw(self.width);
    else return out;
  }
};

void TimeTrace::Node::printPrettyRec(std::ostream& out, NodeFormatOpts& opts)
{

  auto msetw = [&](int i){ return MaybeSetw { opts.align, i }; };

  auto& indent = opts.indent;
  for (int i = 0; i < int(indent.size()) - 1; i++) {
    out << indent[i];
  }
  if (indent.size() > 0) {
    out << (opts.last ? lastChild : internalChild);
  }
  auto percent = [](Duration a, Duration b) {
    return 100 * a / b;
    // auto prec = 100;
    // return double(100 * prec * a / b) / prec;
  };
  auto total = totalDuration();
  auto cnt = measurements.cnt();
  if (opts.parentDuration.isSome()) {
    out << "[" << setw(2) << percent(total, opts.parentDuration.unwrap()) << "%] ";
  }
  if (opts.nameWidth.isSome()) {
    out << msetw(opts.nameWidth.unwrap()) << left;
  }
  out << name << right;


  out << " (total: "<< msetw(4) << total;
  out << ", avg: "  << msetw(4);
  if (cnt == 0) {
    out << "NaN";
  } else {
    out << total / cnt;
  }
  out << ", cnt: "  << msetw(6) << cnt
      << ")" << std::endl;

  // Order a local copy rather than sorting `children` in place: this is called on the
  // timer thread while the main thread may still be scanning and appending to
  // `children` (Lib/Timer.cpp, limitReached()), and an in-place sort would move
  // elements under it. Also makes printing idempotent.
  std::vector<Node*> ordered;
  ordered.reserve(children.size());
  for (auto& c : children) {
    ordered.push_back(&*c);
  }
  std::sort(ordered.begin(), ordered.end(), [](Node* l, Node* r) { return l->totalDuration() > r->totalDuration(); });

  indent.push_back(indentBeforeLast);
  auto copts = opts.child(*this);
  for (unsigned i = 0; i < ordered.size(); i++) {
    copts.last = i == ordered.size() - 1;
    if (copts.last) {
      indent.back() = indentAfterLast;
    }
    ordered[i]->printPrettyRec(out, copts);
  }
  indent.pop_back();
}

struct TimeTrace::Node::FlattenState {
  // std::vector, not Lib::Stack: flatten() runs on the timer thread, see Node
  std::vector<unique_ptr<Node>> nodes;
  std::vector<Node*> recPath;
};

TimeTrace::Node TimeTrace::Node::flatten()
{
  FlattenState s;
  flatten_(s);
  auto root = Node(name);
  root.children = std::move(s.nodes);
  root.measurements = measurements;
  return root;
}

TimeTrace::Node TimeTrace::Node::clone() const 
{
  auto out = Node(name);
  out.measurements = measurements;
  out.children.reserve(children.size());
  for (auto& c : children) {
    out.children.push_back(make_unique<TimeTrace::Node>(c->clone()));
  }
  return out;
}

void TimeTrace::Node::_focus(const char* name, Node& newRoot)
{
  if (strcmp(this->name,  name) == 0) {
    newRoot.extendWith(*this);
  } else {
    for (auto& c : this->children) {
      c->_focus(name, newRoot);
    }
  }
}

void TimeTrace::Node::extendWith(TimeTrace::Node const& other)
{
  ASS(strcmp(other.name, name) == 0)
  measurements.extend(other.measurements);
  for (auto& c : other.children) {
    Node* found = nullptr;
    for (auto& n : this->children) {
      if (n->name == c->name) {
        found = &*n;
        break;
      }
    }
    if (found) {
      found->extendWith(*c);
    } else {
      this->children.push_back(make_unique<TimeTrace::Node>(c->clone()));
    }
  }
}

TimeTrace::Node TimeTrace::Node::focus(const char* name)
{
  FlattenState s;
  auto root = Node(name);
  _focus(name, root);
  return root;
}

void TimeTrace::Node::flatten_(FlattenState& s)
{

  for (auto& c : children) {
    Node* node = nullptr;
    for (auto& n : s.nodes) {
      if (n->name == c->name) {
        node = &*n;
        break;
      }
    }
    if (!node) {
      s.nodes.push_back(make_unique<Node>(c->name));
      node = &*s.nodes.back();
    }

    bool onPath = false;
    for (auto* x : s.recPath) {
      if (x->name == c->name) {
        onPath = true;
        break;
      }
    }
    if (!onPath) {
      // prevent double counting time
      node->measurements.extend(c->measurements);
    }

    s.recPath.push_back(&*c);
    c->flatten_(s);
    s.recPath.pop_back();
  }
}

void TimeTrace::printPretty(std::ostream& out)
{

  auto now = Clock::now();
  for (auto& x : _stack) {
    auto node = get<0>(x);
    auto start = get<1>(x);
    node->measurements.add(now - start);
  }

  auto& root = _tmpRoots.empty() ? _root : *_tmpRoots.back();
  std::vector<const char*> indent;
  auto rootOpts = Node::NodeFormatOpts::root(indent);

  out << "===== start of time trace =====" << std::endl;
  rootOpts.align = false;
  root.printPrettyRec(out, rootOpts);
  out << "===== end of time trace =====" << std::endl;

  out <<                                                  std::endl;

  out << "===== start of flattened time profile =====" << std::endl;
  rootOpts.align = true;
  root.flatten().printPrettyRec(out, rootOpts);
  out << "===== end of flattened time profile =====" << std::endl;


  for (auto& x : _stack) {
    auto node = get<0>(x);
    auto start = get<1>(x);
    node->measurements.remove(now - start);
  }

  if (!env.options->timeStatisticsFocus().empty()) {
    out <<                                                  std::endl;

    auto focus = root.focus(env.options->timeStatisticsFocus().c_str());
    out << "===== start of focussed time profile =====" << std::endl;
    rootOpts.align = false;
    focus.printPrettyRec(out, rootOpts);
    out << "===== end of focussed time profile =====" << std::endl;

    out << "===== start of flattened focussed time profile =====" << std::endl;
    rootOpts.align = true;
    focus.flatten().printPrettyRec(out, rootOpts);
    out << "===== end of flattened focussed time profile =====" << std::endl;
  }
}

} // namespace Shell

#endif // VTIME_PROFILING
