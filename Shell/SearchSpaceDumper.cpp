#ifdef __FEATURE_SEARCH_SPACE_DUMPER
#include "SearchSpaceDumper.hpp"
#include <iostream>
#include "Forwards.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Options.hpp"
#include "Lib/json.hpp"
#include "Kernel/Signature.hpp"
#include <vector>

using namespace nlohmann;
using namespace Kernel;
using namespace Shell;
using namespace std;
using Symbol =  Signature::Symbol;

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

// unsigned serialize(map<void*, unsigned> indices, vector<json>& objects, const Literal& l) {
//   BYPASSING_ALLOCATOR
//     
//     { "pos", l.isPositive() },
//   };
// }

#define SETUP_SERIAlIZE(key, map, key_t) \
  BYPASSING_ALLOCATOR \
  key_t ref = key; \
  auto iter = map.find(ref); \
  if (iter != map.end()) { \
    return iter->second; \
  } \
  auto idx = objects.size(); \
  map[ref] = idx; \
  objects.push_back(json()); \

template<class A>
unsigned serialize(map<const void*, unsigned>& indices, map<unsigned, unsigned>& functors, vector<json>& objects, const A& self);

struct polymorphic_serialize {
  map<const void*, unsigned>& indices;
  map<unsigned, unsigned>& functors;
  vector<json>& objects;
  template<class B>
  unsigned operator()(const B& ser) { return serialize(indices, functors, objects, ser); }
};

template<class A>
unsigned serialize(map<const void*, unsigned>& indices, std::map<unsigned, unsigned>& functors, vector<json>& objects, const A& self) {
  SETUP_SERIAlIZE(&self, indices, const void*)

  objects[idx] = _serialize(self, polymorphic_serialize{ 
      .indices = indices,
      .functors = functors,
      .objects = objects, 
      });

  return idx;
}

struct Function;
struct Predicate;
struct Predicate {
  unsigned functor;
};

struct Function {
  unsigned functor;
};

// template<class Ser> json _serializeInterpreted(const Functor& functor, Ser serial) {
//   if (theo)
// }
#define __SER_CONST__Predicate 

#define __SER_CONST__Function_(ConstantType) \
  { \
    ConstantType c; \
    if (theory->tryInterpretConstant(&fun, c)) { \
      return true; \
    } \
  } \

bool isIntConstant(const Term& fun) {
  __SER_CONST__Function_(IntegerConstantType)
  __SER_CONST__Function_(RationalConstantType)
  __SER_CONST__Function_(RealConstantType)
  return false;
}

#define __SER_CONST__Function \
  j["intConst"] = isIntConstant(self.functor);

#define _SERIALIZE_FUN_PRED(pred, Predicate) \
template<class Ser> json _serialize(const Predicate& self, Ser serial) { \
  json j; \
  j["name"] = env.signature->get ## Predicate(self.functor)->name(); \
  json inter; \
  if (theory->isInterpreted ## Predicate(self.functor)) { \
    inter = theory->interpret ## Predicate(self.functor);\
  } \
  j["inter"] = inter; \
  return {pred, j}; \
} \

_SERIALIZE_FUN_PRED("pred", Predicate)
_SERIALIZE_FUN_PRED("fun", Function)

template<class Ser> json _serialize(const Term& self, Ser serial) {
  json j;
  Function fun = {.functor = self.functor()};
  j["fun"] = serial(fun);
  vector<unsigned> terms;
  for (int i = 0; i < self.arity(); i++) {
    terms.push_back(serial(self[i]));
  }
  j["terms"] = terms;
  j["numConst"] = isIntConstant(self);
  return { "cterm", j };
}

template<class Ser> json _serialize(const TermList& self, Ser serial) {
  json j; 
  if (self.isTerm()) {
    j = serial(*self.term());
  } else if (self.isVar()) {
    j = { "var", self.var()};
  } else {
    ASSERTION_VIOLATION
  }
  return { "term", j };
}

template<class Ser> json _serialize(const Clause& self, Ser serial) {
  json j;
  j["thry_desc"] = self.isTheoryDescendant();

  json lits = json::array();
  for (int i = 0; i < self.size(); i++) {
    lits[i] = serial(*self[i]);
  }

  j["lits"] = lits;
  return { "clause", j };
}


template<class Ser> json _serialize(const Literal& self, Ser serial) {
  json j;
  j["pos"] = self.isPositive();
  Predicate p {.functor = self.functor()};
  j["pred"] = serial(p);
  vector<unsigned> terms;
  for (int i = 0; i < self.arity(); i++) {
    terms.push_back(serial(self[i]));
  }
  j["terms"] = terms;
  return { "lit", j };
}

// unsigned serialize(map<const void*, unsigned> indices, vector<json>& objects, const Clause& self) {
//   SETUP_SERIAlIZE(self)
//
//   json j;
//   j["thryDesc"] = self.isTheoryDescendant();
//   json lits = json::array();
//   // for (int i = 0; i < self.size(); i++) {
//   //   lits[i] = toJson(*self[i]);
//   // }
//   j["lits"] = lits;
//   objects[idx] = { "clause" , j };
//
//   return idx;
// }

template<>
unsigned serialize<Function>(map<const void*, unsigned>& indices,std::map<unsigned, unsigned>& functors, vector<json>& objects, const Function& self) {
  SETUP_SERIAlIZE(self.functor, functors, unsigned)

  objects[idx] = _serialize(self, polymorphic_serialize{ 
      .indices = indices,
      .functors = functors,
      .objects = objects, 
      });

  return idx;
}


void SearchSpaceDumper::dumpFile(const vstring& out) const 
{
  cout << "######################################### dump " << env.options->searchSpaceOutput() << endl;
  BYPASSING_ALLOCATOR
  std::map<const void*, unsigned> indices;
  std::map<unsigned, unsigned> functors;
  std::vector<json> objs;

  for (auto c : _clauses) {
    serialize(indices, functors, objs, *c);
  }
  cout << json(objs) << endl;
  
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
