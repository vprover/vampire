#include "Shell/TimeTracing.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"

namespace Shell {

using namespace Lib;

TimeTrace::TimeTrace() 
  : _root("<root>")
  , _stack({ {&_root, Clock::now(), }, }) 
{  }

TimeTrace::ScopedTimer::ScopedTimer(const char* name)
  : ScopedTimer(env.statistics->timeTrace, name)
{ }

TimeTrace::ScopedTimer::ScopedTimer(TimeTrace& trace, const char* name)
  : _trace(trace)
#if VDEBUG
  , _start()
  , _name(name)
#endif
{
  // DBG("ScopedTimer() ", name)
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

TimeTrace::ScopedTimer::~ScopedTimer()
{
  auto now = Clock::now();
  auto cur = _trace._stack.pop();
  auto node = get<0>(cur);
  auto start = get<1>(cur);
  node->measurements.push(now  - start);
  ASS_EQ(node->name, _name);
  ASS(start == _start);
}

TimeTrace::Duration TimeTrace::Node::totalDuration() const
{ return iterTraits(measurements.iter())
           .fold(Duration::zero(), 
                 [](Duration l, Duration r){ return l + r; }); }

const char* TimeTrace::Groups::PREPROCESSING = "preprocessing";
const char* TimeTrace::Groups::PARSING = "parsing";
const char* TimeTrace::Groups::LITERAL_ORDER_AFTERCHECK = "literal order aftercheck";

void TimeTrace::Node::print(std::ostream& out, unsigned indent, Option<Node const&> parent)
{
  for (unsigned i = 0; i < indent; i++) {
    out << "  ";
  }
  auto percent = [](Duration a, Duration b) {
    auto prec = 100;
    return double(100 * prec * a / b) / prec;
  };
  auto total = totalDuration();
  if (parent.isSome()) {
    out << percent(total, parent.unwrap().totalDuration()) << " % ";
  }
  auto cnt = measurements.size();
  out << name
      << " (total: " << std::chrono::duration_cast<std::chrono::milliseconds>(total).count() << " ms"
      << ", cnt: " << cnt 
      << ", avg: " << std::chrono::duration_cast<std::chrono::microseconds>(total / cnt).count() << " μs"
      << ")"
      << std::endl;
  std::sort(children.begin(), children.end(), [](auto& l, auto& r) { return l->totalDuration() > r->totalDuration(); });
  for (auto& c : children) {
    c->print(out, indent + 1, Option<Node const&>(*this));
  }
}

void TimeTrace::print(std::ostream& out)
{
  out << "Time trace: " << std::endl;
  auto now = Clock::now();
  for (auto& x : _stack) {
    auto node = get<0>(x);
    auto start = get<1>(x);
    node->measurements.push(now - start);
  }
  _root.print(out, /* indent */ 0, Option<Node const&>());
  for (auto& x : _stack) {
    get<0>(x)->measurements.pop();
  }
}

} // namespace Shell
