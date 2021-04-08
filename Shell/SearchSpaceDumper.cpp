#ifdef __FEATURE_SEARCH_SPACE_DUMPER

#include "SearchSpaceDumper.hpp"
#include <iostream>
#include "Forwards.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Options.hpp"
#include "Lib/json.hpp"
#include "Kernel/Signature.hpp"
#include <vector>
#include <fstream>

#define DEBUG(...) DBG(__VA_ARGS__)
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

template<class Key>
struct JsonMap 
{
  map<Key, unsigned> ids;
  vector<json> values;
};

struct SerializationContext 
{

  JsonMap<Clause const*> clauses;
  JsonMap<Literal const*> literals;
  JsonMap<Term const*> cterms;
  JsonMap<TermList> terms;
  JsonMap<unsigned> functions;
  JsonMap<unsigned> predicates;

  SerializationContext() {}
  SerializationContext(SerializationContext const&) = delete;

  template<class B>
  unsigned operator()(const B& ser) { return serialize(*this, ser); }

  void tegrity() {
    auto teg = [](vector<json>& vec) {
      for(int i = 0; i < vec.size(); i++) { 
        ASS_REP(vec[i] != nullptr, i) 
        ASS_REP(vec[i] != json(), i) 
      }
      for(auto& x : vec) { 
        ASS(x != nullptr) 
        ASS(x != json()) 
      }
    };
    teg(clauses   .values);
    teg(literals  .values);
    teg(cterms    .values);
    teg(terms     .values);
    teg(functions .values);
    teg(predicates.values);
  }

  json toJson() &&
  {
    json out;
    tegrity();
    out["clauses"]    = std::move(clauses.values);
    out["literals"]   = std::move(literals.values);
    out["cterms"]     = std::move(cterms.values);
    out["terms"]      = std::move(terms.values);
    out["functions"]  = std::move(functions.values);
    out["predicates"] = std::move(predicates.values);
    return out;
  }
};

struct Predicate 
{ unsigned functor; };

std::ostream& operator<<(std::ostream& out, Predicate const& self) 
{ return out << self.functor; }

struct Function 
{
  unsigned functor;
  const Term& term;
};

std::ostream& operator<<(std::ostream& out, Function const& self) 
{ return out << self.functor; }

#define __SER_CONST__Predicate 

#define __SER_CONST__Function_(ConstantType, key, ...)                                                        \
  {                                                                                                           \
    ConstantType c;                                                                                           \
    if (theory->tryInterpretConstant(&fun, c)) {                                                              \
      json j;                                                                                                 \
      j[key] = __VA_ARGS__;                                                                                   \
      return j;                                                                                               \
    }                                                                                                         \
  }                                                                                                           \

json trySerializeNumber(const Term& fun) {
  __SER_CONST__Function_(IntegerConstantType, "Int", c.toInner())
  __SER_CONST__Function_(RationalConstantType, "Rat", vector<int>{ c.numerator().toInner(), c.denominator().toInner() })
  __SER_CONST__Function_(RealConstantType, "Real", vector<int>{ c.numerator().toInner(), c.denominator().toInner() })
  return json();
}

const char* serializeInterpretation(Interpretation i) {
#define CASE(pref, suff, expr)                                                                                \
  case Kernel::Theory::Interpretation::pref ## suff: return expr;                                             \

#define NUM_CASES(SORT)                                                                                       \
    CASE(SORT, _GREATER , "Greater")                                                                          \
    CASE(SORT, _GREATER_EQUAL , "GreaterEqual")                                                               \
    CASE(SORT, _LESS , "Less")                                                                                \
    CASE(SORT, _LESS_EQUAL , "LessEqual")                                                                     \
                                                                                                              \
    CASE(SORT, _UNARY_MINUS, "Neg")                                                                           \
    CASE(SORT, _PLUS, "Add")                                                                                  \
    CASE(SORT, _MINUS, "Sub")                                                                                 \
    CASE(SORT, _MULTIPLY, "Mul")                                                                              \
    CASE(SORT, _QUOTIENT_E, "QuotientE")                                                                      \
    CASE(SORT, _QUOTIENT_T, "QuotientT")                                                                      \
    CASE(SORT, _QUOTIENT_F, "QuotientF")                                                                      \
    CASE(SORT, _REMAINDER_E, "RemainderE")                                                                    \
    CASE(SORT, _REMAINDER_T, "RemainderT")                                                                    \
    CASE(SORT, _REMAINDER_F, "RemainderF")                                                                    \
    CASE(SORT, _FLOOR, "Floor")                                                                               \
    CASE(SORT, _CEILING, "Ceiling")                                                                           \
    CASE(SORT, _TRUNCATE, "Truncate")                                                                         \
    CASE(SORT, _ROUND, "Round")                                                                               \


#define _CONVERSIONS(SORT, _CONV_, str)                                                                       \
  CASE(INT, _CONV_##SORT, str)                                                                                \
  CASE(RAT, _CONV_##SORT, str)                                                                                \
  CASE(REAL, _CONV_##SORT, str)                                                                               \

#define CONVERSIONS(_CONV_, str)                                                                              \
    _CONVERSIONS(INT , _CONV_, str)                                                                           \
    _CONVERSIONS(RAT , _CONV_, str)                                                                           \
    _CONVERSIONS(REAL, _CONV_, str)                                                                           \

#define FRAC_CASES(SORT)                                                                                      \
  CASE(SORT, _QUOTIENT, "Quot")

  switch (i) {
    case Kernel::Theory::Interpretation::EQUAL: return "Eq";
    case Kernel::Theory::Interpretation::INVALID_INTERPRETATION: return "Invalid";

    /* integers */
    NUM_CASES(INT)
    CASE(INT , _ABS    , "Abs")
    CASE(INT, _DIVIDES, "Divides") 
    CASE(INT, _SUCCESSOR , "Successor") 

    /* rationals */
    NUM_CASES(RAT)
    FRAC_CASES(RAT)

    /* reals */
    NUM_CASES(REAL)
    FRAC_CASES(REAL)

    /* numeric conversion functions */
    CONVERSIONS(_IS_, "IsType")
    CONVERSIONS(_TO_, "ToType")

    /* arrays */
    CASE(ARRAY, _SELECT, "Select")
    CASE(ARRAY_BOOL, _SELECT, "Select")
    CASE(ARRAY, _STORE, "Store")
  }
}

#define IF_FUN_Predicate(...)
#define IF_FUN_Function(...) __VA_ARGS__

#define _SERIALIZE_FUN_PRED(Predicate)                                                                  \
  json j;                                                                                                     \
  j["name"] = env.signature->get ## Predicate(self.functor)->name();                                          \
  json inter;                                                                                                 \
  if (theory->isInterpreted ## Predicate(self.functor)) {                                                     \
    inter = serializeInterpretation(theory->interpret ## Predicate(self.functor));                            \
  }                                                                                                           \
  IF_FUN_ ## Predicate (                                                                                      \
    else {                                                                                                    \
      inter = trySerializeNumber(self.term);                                                                  \
    }                                                                                                         \
  )                                                                                                           \
                                                                                                              \
  j["inter"] = inter;                                                                                         \
  return j;                                                                                           \

template<class C> struct SerializeCached;

template<> struct SerializeCached<Clause>
{ 
  static auto id      (Clause const& c)           -> Clause const*          { return &c;          }
  static auto getCache(SerializationContext& ser) -> decltype(ser.clauses)& { return ser.clauses; }
  static auto toJson(Clause const& self, SerializationContext& serial) -> json {
    json j;
    j["thry_desc"] = self.isPureTheoryDescendant();

    json lits = json::array();
    for (int i = 0; i < self.size(); i++) {
      lits[i] = serial(*self[i]);
    }

    j["lits"] = lits;
    return j;
  }
};

template<> struct SerializeCached<Literal>
{ 
  static auto id      (Literal const& x)          -> Literal const*          { return &x;           }
  static auto getCache(SerializationContext& ser) -> decltype(ser.literals)& { return ser.literals; }
  static auto toJson(Literal const& self, SerializationContext& serial) -> json {
    json j;
    j["pos"] = self.isPositive();
    Predicate p {.functor = self.functor()};
    j["pred"] = serial(p);
    vector<unsigned> terms;
    for (int i = 0; i < self.arity(); i++) {
      auto x  = serial(self[i]);
      // DBG(self[i].toString()," -> ", x)
      terms.push_back(x);
    }
    j["args"] = terms;
    return j;
  }
};

template<> struct SerializeCached<Term>
{ 
  static auto id      (Term const& x)             -> Term const*           { return &x;        }
  static auto getCache(SerializationContext& ser) -> decltype(ser.cterms)& { return ser.cterms; }
  static auto toJson(Term const& self, SerializationContext& serial) -> json {
    json j;
    Function fun = { .functor = self.functor(), .term = self };
    j["fun"] = serial(fun);
    vector<unsigned> terms;
    terms.reserve(self.arity());
    for (int i = 0; i < self.arity(); i++) {
      terms.push_back(serial(self[i]));
    }
    j["args"] = std::move(terms);
    return j;
  }
};

template<> struct SerializeCached<Predicate>
{ 
  static auto id      (Predicate const& x)         -> decltype(x.functor)       { return x.functor;   }
  static auto getCache(SerializationContext& ser) -> decltype(ser.predicates)& { return ser.predicates; }
  static auto toJson(Predicate const& self, SerializationContext& sef) -> json 
  { _SERIALIZE_FUN_PRED(Predicate) }
};

template<> struct SerializeCached<Function>
{ 
  static auto id      (Function const& x)          -> decltype(x.functor)      { return x.functor;   }
  static auto getCache(SerializationContext& ser) -> decltype(ser.functions)& { return ser.functions; }
  static auto toJson(Function const& self, SerializationContext& sef) -> json 
  { _SERIALIZE_FUN_PRED(Function) }
};

template<> struct SerializeCached<TermList> 
{ 
  static auto id      (TermList const& x)         -> TermList      { return x;   }
  static auto getCache(SerializationContext& ser) -> decltype(ser.terms)& { return ser.terms; }
  static auto toJson(TermList const& self, SerializationContext& serial) -> json {
    json j; 
    if (self.isTerm()) {
      j["T"] = serial(*self.term());
    } else if (self.isVar()) {
      j["V"] = self.var();
    } else {
      ASSERTION_VIOLATION
    }
    return j;
  }
};

template<class C>
unsigned setupKey(SerializationContext& ctxt, C const& self)
{
    BYPASSING_ALLOCATOR
      
    auto& cache = SerializeCached<C>::getCache(ctxt);
    auto id = SerializeCached<C>::id(self);
    auto iter = cache.ids.find(id);
    if (iter != cache.ids.end()) {
      auto idx = iter->second;
      return idx;
    }
    unsigned idx = cache.values.size();
    cache.ids[id] = idx;
    cache.values.push_back(nullptr);
    return idx;
};

static bool shallCheckTegrity = false;

#define CHECK_TEGRITY(ctxt) \
  if (shallCheckTegrity) \
    ASS(ctxt.cterms.values[13] != nullptr) \

template<class C>
unsigned serialize(SerializationContext& ctxt, C const& self) 
{
  auto idx = setupKey<C>(ctxt, self);
  

  if (SerializeCached<C>::getCache(ctxt).values[idx] == nullptr) {
    SerializeCached<C>::getCache(ctxt).values[idx] = SerializeCached<C>::toJson(self, ctxt);
  }
  if (idx == 13 && std::is_same<C, Term>::value) {
    shallCheckTegrity = true;
  }

  return idx;
};

void SearchSpaceDumper::dumpFile(const vstring& out) const 
{
  CALL("SearchSpaceDumper::dumpFile")
  DEBUG("dumping searchspace to file ", env.options->searchSpaceOutput());
  BYPASSING_ALLOCATOR

  SerializationContext ctxt;

  DEBUG("preprocessing...");
  for (auto c : _clauses) {
    serialize(ctxt, *c);
  }
  DEBUG("converting to json...")
  auto json = std::move(ctxt).toJson();
  DEBUG("writing to ", out, "...");
  cout << out.c_str() << endl;
  ofstream f{ out.c_str() };
  f << json << endl; 

  DEBUG("finished.");
}

void SearchSpaceDumper::add(Kernel::Clause* clause) 
{
  clause->incRefCnt();
  _clauses.push(clause); 
}

} // namespace Shell

#endif
