#ifdef __FEATURE_SEARCH_SPACE_DUMPER
#include "SearchSpaceDumper.hpp"
#include <iostream>
#include "Forwards.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Options.hpp"
#include "Lib/json.hpp"
using namespace nlohmann;
using namespace Kernel;
using namespace Shell;

#define UNIMPLEMENTED ASSERTION_VIOLATION

namespace Shell {

SearchSpaceDumper* SearchSpaceDumper::_instance = NULL;

SearchSpaceDumper* SearchSpaceDumper::instance() {
  return _instance;
}

void SearchSpaceDumper::init() {
  ASS(!(_instance))
  _instance = new SearchSpaceDumper();
}

SearchSpaceDumper::SearchSpaceDumper() : _clauses(decltype(_clauses)())
{ 
}

SearchSpaceDumper::~SearchSpaceDumper()
{ 
  for (auto c : _clauses) {
    c->decRefCnt();
  }
}

json toJson(const Literal& l) {
  BYPASSING_ALLOCATOR
  return {
    { "pos", l.isPositive() },
  };
}

json toJson(const Clause& cl) {
  BYPASSING_ALLOCATOR
  json j;
  j["thryDesc"] = cl.isTheoryDescendant();
  json lits = json::array();
  for (int i = 0; i < cl.size(); i++) {
    lits[i] = toJson(*cl[i]);
  }
  j["lits"] = lits;

  return j;
}

void SearchSpaceDumper::dumpFile(const vstring& out) const 
{
  cout << "######################################### dump " << env.options->searchSpaceOutput() << endl;
  BYPASSING_ALLOCATOR

  for (auto c : _clauses) {
    cout << toJson(*c) << endl;
  }
  
  // pk.pack(std::string("Log message .packer 1"));
  // pk.pack(std::string("Log message ... 2"));
  // pk.pack(std::string("Log message ... 3"));

}
void SearchSpaceDumper::add(Kernel::Clause* clause) 
{
  clause->incRefCnt();
  _clauses.push(clause); 
}

} // namespace Shell

#endif
