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

namespace Shell {

using namespace Lib;

// TODO: these should be dispensable with C++17 onwards
const char* const TimeTrace::CLAUSE_GENERATION;
const char* const TimeTrace::CONSEQUENCE_FINDING;
const char* const TimeTrace::FMB_DEFINITION_INTRODUCTION;
const char* const TimeTrace::HYPER_SUP;
const char* const TimeTrace::LITERAL_ORDER_AFTERCHECK;
const char* const TimeTrace::PARSING;
const char* const TimeTrace::PASSIVE_CONTAINER_MAINTENANCE;
const char* const TimeTrace::PREPROCESSING;
const char* const TimeTrace::PROPERTY_EVALUATION;
const char* const TimeTrace::AVATAR_SAT_SOLVER;
const char* const TimeTrace::SHUFFLING;
const char* const TimeTrace::SINE_SELECTION;
const char* const TimeTrace::TERM_SHARING;

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
#if VDEBUG
  , _start()
  , _name(name)
#endif
{
  if (_trace._enabled) {
    auto& children = std::get<0>(trace._stack.top())->children;
    auto node = iterTraits(children.iter())
      .map([](auto& x) { return &*x; })
      .find([&](Node* n) { return n->name == name; })
      .unwrapOrElse([&]() { 
          children.push(Lib::make_unique<Node>(name));
          return &*children.top();
      });
    auto start = Clock::now();
#if VDEBUG
    _start = start;
#endif 

    _trace._stack.push(std::make_pair(node, start));
  }
}

TimeTrace TimeTrace::_instance;

void TimeTrace::setEnabled(bool v) 
{ _enabled = v; }

TimeTrace::ScopedTimer::~ScopedTimer()
{
  if (_trace._enabled) {
    auto now = Clock::now();
    auto cur = _trace._stack.pop();
    auto node = get<0>(cur);
    auto start = get<1>(cur);
    node->measurements.add(now  - start);
    ASS_EQ(node->name, _name);
    ASS(start == _start);
  }
}


TimeTrace::ScopedChangeRoot::ScopedChangeRoot()
  : ScopedChangeRoot(TimeTrace::instance())
{ }

TimeTrace::ScopedChangeRoot::ScopedChangeRoot(TimeTrace& trace)
  : _trace(trace)
{
  if (_trace._enabled) {
    _trace._tmpRoots.push(get<0>(trace._stack.top()));
  }
}

TimeTrace::ScopedChangeRoot::~ScopedChangeRoot()
{
  if (_trace._enabled) {
    _trace._tmpRoots.pop();
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
  Kernel::Stack<const char*>& indent;
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
               ? iterTraits(parent.children.iter())
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
  BYPASSING_ALLOCATOR
  if (opts.nameWidth.isSome()) {
    out << msetw(opts.nameWidth.unwrap()) << left;
  }
  out << name << right;

  out << " (total: "<< msetw(4) << total
      << ", avg: "  << msetw(4) << total / cnt
      << ", cnt: "  << msetw(6) << cnt
      << ")" << std::endl;
  std::sort(children.begin(), children.end(), [](auto& l, auto& r) { return l->totalDuration() > r->totalDuration(); });
  indent.push(indentBeforeLast);
  auto copts = opts.child(*this);
  for (unsigned i = 0; i < children.size(); i++) {
    copts.last = i == children.size() - 1;
    if (copts.last) {
      indent.top() = indentAfterLast;
    }
    children[i]->printPrettyRec(out, copts);
  }
  indent.pop();
}

struct TimeTrace::Node::FlattenState {
  Stack<unique_ptr<Node>> nodes;
  Stack<Node*> recPath;
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

void TimeTrace::Node::flatten_(FlattenState& s)
{

  for (auto& c : children) {
    auto node_ = iterTraits(s.nodes.iter())
      .find([&](auto& n) { return n->name == c->name; });

    if (node_.isNone()) {
      s.nodes.push(make_unique<Node>(c->name));
    }
    auto& node = node_.isSome() ? node_.unwrap() : s.nodes.top();

    if (!iterTraits(s.recPath.iter()).any([&](auto& x) { return x->name == c->name; })) {
      // prevent double counting time
      node->measurements.extend(c->measurements);
    }

    s.recPath.push(&*c);
    c->flatten_(s);
    s.recPath.pop();
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

  auto& root = _tmpRoots.size() == 0 ? _root : *_tmpRoots.top();
  Stack<const char*> indent;
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
}

} // namespace Shell

#endif // VTIME_PROFILING
