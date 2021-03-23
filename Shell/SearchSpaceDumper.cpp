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

struct SerializationContext 
{
  map<Clause const*, unsigned> clauses;
  map<Literal const*, unsigned> literals;
  map<Term const*, unsigned> terms;
  map<unsigned, unsigned> functions;
  map<unsigned, unsigned> predicates;

  vector<json> objects;

  SerializationContext() {}
  SerializationContext(SerializationContext const&) = delete;

  template<class B>
  unsigned operator()(const B& ser) { return serialize(*this, ser); }

  json toJson() const 
  {
    return json(objects);
  }
};

struct Predicate 
{ unsigned functor; };

struct Function 
{
  unsigned functor;
  const Term& term;
};

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

#define _SERIALIZE_FUN_PRED(pred, Predicate)                                                                  \
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
  return {pred, j};                                                                                           \

template<class C> struct SerializeCached;

template<> struct SerializeCached<Clause>
{ 
  static constexpr bool value = true; 
  static auto id      (Clause const& c)           -> Clause const*          { return &c;          }
  static auto getCache(SerializationContext& ser) -> decltype(ser.clauses)& { return ser.clauses; }
  static auto toJson(Clause const& self, SerializationContext& serial) -> tuple<const char*, json> {
    json j;
    j["thry_desc"] = self.isPureTheoryDescendant();

    json lits = json::array();
    for (int i = 0; i < self.size(); i++) {
      lits[i] = serial(*self[i]);
    }

    j["lits"] = lits;
    return { "Clause", j };
  }
};

template<> struct SerializeCached<Literal>
{ 
  static constexpr bool value = true; 
  static auto id      (Literal const& x)          -> Literal const*          { return &x;           }
  static auto getCache(SerializationContext& ser) -> decltype(ser.literals)& { return ser.literals; }
  static auto toJson(Literal const& self, SerializationContext& serial) -> tuple<const char*, json> {
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
    j["terms"] = terms;
    return { "Lit", j };
  }
};

template<> struct SerializeCached<Term>
{ 
  static constexpr bool value = true; 
  static auto id      (Term const& x)             -> Term const*          { return &x;        }
  static auto getCache(SerializationContext& ser) -> decltype(ser.terms)& { return ser.terms; }
  static auto toJson(Term const& self, SerializationContext& serial) -> tuple<const char*, json> {
    json j;
    Function fun = {.functor = self.functor(), .term = self};
    j["fun"] = serial(fun);
    vector<unsigned> terms;
    for (int i = 0; i < self.arity(); i++) {
      terms.push_back(serial(self[i]));
    }
    j["terms"] = terms;
    return { "Cterm", j };
  }
};

template<> struct SerializeCached<Predicate>
{ 
  static constexpr bool value = true; 
  static auto id      (Predicate const& x)         -> decltype(x.functor)       { return x.functor;   }
  static auto getCache(SerializationContext& ser) -> decltype(ser.predicates)& { return ser.predicates; }
  static auto toJson(Predicate const& self, SerializationContext& sef) -> tuple<const char*, json> 
  { _SERIALIZE_FUN_PRED("Pred", Predicate) }
};

template<> struct SerializeCached<Function>
{ 
  static constexpr bool value = true; 
  static auto id      (Function const& x)          -> decltype(x.functor)      { return x.functor;   }
  static auto getCache(SerializationContext& ser) -> decltype(ser.functions)& { return ser.functions; }
  static auto toJson(Function const& self, SerializationContext& sef) -> tuple<const char*, json> 
  { _SERIALIZE_FUN_PRED("Fun", Function) }
};

template<> struct SerializeCached<TermList> 
{ 
  static constexpr bool value = false; 
  static auto toJson(TermList const& self, SerializationContext& serial) -> tuple<const char*, json> {
    json j; 
    if (self.isTerm()) {
      j["Cterm"] = serial(*self.term());
    } else if (self.isVar()) {
      j["Var"] = self.var();
    } else {
      ASSERTION_VIOLATION
    }
    return { "Term", j };
  }
};

template<class C, typename std::enable_if<SerializeCached<C>::value, bool>::type = true>
unsigned setupKey(SerializationContext& ctxt, C const& self) 
{
    BYPASSING_ALLOCATOR                    
    auto& cache = SerializeCached<C>::getCache(ctxt);          
    auto id = SerializeCached<C>::id(self);
    auto iter = cache.find(id);              
    if (iter != cache.end()) {                 
      return iter->second;                      
    }                                            
    unsigned idx = ctxt.objects.size();
    cache[id] = idx;                    
    ctxt.objects.push_back(json()); 
    return idx;
};

template<class C, typename std::enable_if<!SerializeCached<C>::value, bool>::type = true>
unsigned setupKey(SerializationContext& ctxt, C const& self) 
{
    BYPASSING_ALLOCATOR                
    auto idx = ctxt.objects.size();
    ctxt.objects.push_back(json());
    return idx;
};

template<class C>
unsigned serialize(SerializationContext& ctxt, C const& self) 
{
  unsigned idx = setupKey<C>(ctxt, self);
                                                        
  auto ser = SerializeCached<C>::toJson(self, ctxt);                   
                                                          
  json j;                                                  
  j[get<0>(ser)] = get<1>(ser);                             
                                                             
  ctxt.objects[idx] = j;                                 
                                                               
  return idx;
};

void SearchSpaceDumper::dumpFile(const vstring& out) const 
{
  CALL("SearchSpaceDumper::dumpFile")
  DBG("dumping searchspace to file ", env.options->searchSpaceOutput());
  BYPASSING_ALLOCATOR

  SerializationContext ctxt;

  DBG("serializing...");
  for (auto c : _clauses) {
    serialize(ctxt, *c);
  }
  DBG("writing...");
  cout << out.c_str() << endl;
  ofstream f{ out.c_str() };

  f << ctxt.toJson().dump(3) << endl; 

  DBG("finished.");
}

void SearchSpaceDumper::add(Kernel::Clause* clause) 
{
  clause->incRefCnt();
  _clauses.push(clause); 
}

} // namespace Shell

#endif
