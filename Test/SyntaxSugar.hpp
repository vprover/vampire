/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**! This file contains macros to provide syntax sugar for building formulas,
 * terms, etc. for test cases.
 *
 * Macros that are not meant to be used from outside of this file are prefixed 
 * with two underscores.
 *
 * @autor Johannes Schoisswohl
 * @date 2020-04-29
 */

#ifndef __TEST__SYNTAX_SUGAR__H__
#define __TEST__SYNTAX_SUGAR__H__

#include<functional>

#include "Forwards.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/NumTraits.hpp"

#include "Indexing/TermSharing.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/OperatorType.hpp"
#include "Shell/TermAlgebra.hpp"

#define __TO_SORT_RAT RationalConstantType::getSort()
#define __TO_SORT_INT IntegerConstantType::getSort()
#define __TO_SORT_REAL RealConstantType::getSort()

#define __CONSTANT_TYPE_INT  IntegerConstantType
#define __CONSTANT_TYPE_REAL RealConstantType
#define __CONSTANT_TYPE_RAT  RationalConstantType
#if defined(__clang__)
#  define __ALLOW_UNUSED(...)                                                                                 \
    _Pragma("GCC diagnostic push")                                                                            \
    _Pragma("GCC diagnostic ignored \"-Wunused\"")                                                            \
    __VA_ARGS__                                                                                               \
    _Pragma("GCC diagnostic pop")                                                                             \

#elif defined(__GNUC__) || defined(__GNUG__)

#  define __ALLOW_UNUSED(...)                                                                                 \
    _Pragma("GCC diagnostic push")                                                                            \
    _Pragma("GCC diagnostic ignored \"-Wunused-but-set-variable\"")                                           \
    __VA_ARGS__                                                                                               \
    _Pragma("GCC diagnostic pop")                                                                             \

#else
#  define __ALLOW_UNUSED(...) __VA_ARGS__             
#endif
 
#define __ARGS_DECL(Type, arity) __ARGS_DECL_ ## arity(Type)
#define __ARGS_DECL_1(Type) Type arg0_ 
#define __ARGS_DECL_2(Type) Type arg0_ , Type arg1_ 

#define __ARGS_EXPR(Type, arity) __ARGS_EXPR_ ## arity(Type)
#define __ARGS_EXPR_1(Type) arg0_
#define __ARGS_EXPR_2(Type) arg0_, arg1_

#if defined(__clang__)
#  define __ALLOW_UNUSED(...)                                                                                 \
    _Pragma("GCC diagnostic push")                                                                            \
    _Pragma("GCC diagnostic ignored \"-Wunused\"")                                                            \
    __VA_ARGS__                                                                                               \
    _Pragma("GCC diagnostic pop")                                                                             \

#elif defined(__GNUC__) || defined(__GNUG__)

#  define __ALLOW_UNUSED(...)                                                                                 \
    _Pragma("GCC diagnostic push")                                                                            \
    _Pragma("GCC diagnostic ignored \"-Wunused-but-set-variable\"")                                           \
    __VA_ARGS__                                                                                               \
    _Pragma("GCC diagnostic pop")                                                                             \

#else
#  define __ALLOW_UNUSED(...) __VA_ARGS__             
#endif
 

#define __CLSR_FUN_INTERPRETED(arity, mul, INT, _MULTIPLY)                                                    \
    auto mul = [](__ARGS_DECL(TermSugar, arity)) -> TermSugar {                                               \
      return TermList(Term::create ## arity(                                                                  \
            env.signature->getInterpretingSymbol(Theory::Interpretation:: INT ## _MULTIPLY),                  \
            __ARGS_EXPR(Type, arity))                                                                         \
          );                                                                                                  \
    };                                                                                                        \

#define __REPEAT_1(sort) sort
#define __REPEAT_2(sort) sort, __REPEAT_1(sort)
#define __REPEAT_3(sort) sort, __REPEAT_2(sort)
#define __REPEAT_4(sort) sort, __REPEAT_3(sort)
#define __REPEAT_5(sort) sort, __REPEAT_4(sort)
#define __REPEAT_6(sort) sort, __REPEAT_5(sort)
#define __REPEAT_7(sort) sort, __REPEAT_6(sort)
#define __REPEAT_8(sort) sort, __REPEAT_7(sort)
#define __REPEAT_9(sort) sort, __REPEAT_8(sort)
#define __REPEAT_10(sort) sort, __REPEAT_9(sort)
#define __REPEAT(arity, sort) __REPEAT_ ## arity(sort)

#define DECL_CONST(f, sort) auto f = ConstSugar(#f, sort);
#define DECL_FUNC(f, ...)   auto f = FuncSugar(#f, __VA_ARGS__);
#define DECL_PRED(f, ...)   auto f = PredSugar(#f, __VA_ARGS__);
#define DECL_SORT(s)        auto s = SortSugar(#s);
#define DECL_VAR(x, i) auto x = TermSugar(TermList::var(i));

#define DECL_DEFAULT_VARS                                                                                     \
  __ALLOW_UNUSED(                                                                                             \
    DECL_VAR(x, 0)                                                                                            \
    DECL_VAR(y, 1)                                                                                            \
    DECL_VAR(z, 2)                                                                                            \
  )                                                                                                           \


/** tldr: For examples on usage see UnitTesting/tSyntaxSugar.cpp
 *
 * This macro provides syntax sugar for building terms and clauses in a one-sorted theory of numbers. 
 *
 * i.e. the theories supported are:
 * NUMBER_SUGAR(Int) ==> integer arithmetic 
 * NUMBER_SUGAR(Rat) ==> rational arithmetic 
 * NUMBER_SUGAR(Real) ==> rational arithmetic 
 *
 * The macro is meant to be called within a TEST_FUN(...){...} block to import the syntax sugar for 
 * the corresponding test case. It provides a class TermSugar that implicitly converts number literals 
 * to terms in the corresponding sort, and operators to build complex terms and literals. Further it sets 
 * some (C++) variables to variable terms and some to constant terms.
 *
 * Additionally the macros `DECL_FUNC`, `DECL_CONST`, and `DECL_PRED` can be 
 * used to declare uninterpreted functions/predicates/constants over the sort.
 *
 * These are the automatically defined operators and variables
 *
 * local variables:
 * x ... variable X0
 * y ... variable X1
 * z ... variable X2
 *
 * Operators for creating complex terms:
 * operator* ... interpreted multiplication
 * operator+ ... interpreted addition
 * operator- ... interpreted unary minus
 *
 * Operators for creating literals:
 * operator>   ... interpreted greater relation
 * operator>=  ... interpreted greater or equal relation
 * operator<   ... interpreted less relation
 * operator<=  ... interpreted less or equal relation
 * operator==  ... interpreted equality relation
 * operator!=  ... interpreted equality relation
 * operator~   ... flipping a literal's polarity
 *
 * Other closures:
 * frac(int,int) ... creates a fractional interpreted constant (only for REAL, and RAT)
 * num(int)      ... explicity converts a number to an interpreted constant 
 *                   this can be needed in order to prevent the compiler from pre-evaluating integer expressions.
 *                   e.g. {
 *                      Literal* l1 = (a == (3 * 2));
 *                                          ^^^^^^^ this will be evaluated to 6 before transforming it into a term
 *                                                  in order to prevent this we can write:
 *                      Literal* l2 = (a == (num(3) * 2));
 *                   }
 *
 * For examples see UnitTesting/tSyntaxSugar.cpp.
 */
#define NUMBER_SUGAR(Sort)                                                                                    \
  __ALLOW_UNUSED(                                                                                             \
    using NumTraits = Sort##Traits;                                                                           \
    syntaxSugarGlobals().setNumTraits(NumTraits{});                                                           \
    auto Sort = SortSugar(NumTraits::sort());                                                                 \
  )

#define DECL_TERM_ALGEBRA(...) createTermAlgebra(__VA_ARGS__);

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// implementation
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
using SortId = TermList;

struct SortSugar 
{
  SortId _srt;

  SortSugar(SortId srt) : _srt(srt) {}
public:
  SortSugar(const char* name) 
    : SortSugar(TermList(AtomicSort::createConstant(name))) 
  {  }

  SortId sortId() const { return _srt; }
};

class TermSugar;

class SyntaxSugarGlobals 
{
  static SyntaxSugarGlobals _instance;

  template<class NumTraits>
  void setAllNumTraits() 
  {
    createNumeral = [](int i) {return NumTraits::constantTl(i);};

    add = NumTraits::add;
    mul = NumTraits::mul;

    minus = NumTraits::minus;

    less = NumTraits::less;
    leq  = NumTraits::leq;
    greater = NumTraits::greater;
    geq  = NumTraits::geq;

    isInt = NumTraits::isInt;
    isRat = NumTraits::isRat;
    isReal = NumTraits::isReal;

  }


  template<class NumTraits>
  void setFracTraits() 
  { 
    setAllNumTraits<NumTraits>();
    div = NumTraits::div; 
    createFraction = [](int a, int b) {return NumTraits::constantTl(a,b);};
  }

public:
  static SyntaxSugarGlobals& instance() {
    return _instance;
  }

  void setNumTraits(IntTraits)
  {
    setAllNumTraits<IntTraits>();

    quotientT = IntTraits::quotientT;
    remainderT = IntTraits::remainderT;
    quotientF = IntTraits::quotientF;
    remainderF = IntTraits::remainderF;
    quotientE = IntTraits::quotientE;
    remainderE = IntTraits::remainderE;
  }

  void setNumTraits(RatTraits)
  { setFracTraits<RatTraits>(); }


  void setNumTraits(RealTraits)
  { setFracTraits<RealTraits>(); }

  std::function<TermList(int, int)> createFraction;
  std::function<TermList(int)> createNumeral;

  std::function<TermList(TermList, TermList)> add;
  std::function<TermList(TermList, TermList)> mul;
  std::function<TermList(TermList, TermList)> div;

  std::function<TermList(TermList, TermList)> quotientT;
  std::function<TermList(TermList, TermList)> remainderT;
  std::function<TermList(TermList, TermList)> quotientF;
  std::function<TermList(TermList, TermList)> remainderF;
  std::function<TermList(TermList, TermList)> quotientE;
  std::function<TermList(TermList, TermList)> remainderE;

  std::function<TermList(TermList)> minus;


  std::function<Literal*(bool, TermList, TermList)> less;
  std::function<Literal*(bool, TermList, TermList)> leq ;
  std::function<Literal*(bool, TermList, TermList)> greater;
  std::function<Literal*(bool, TermList, TermList)> geq ;

  std::function<Literal*(bool, TermList)> isInt;
  std::function<Literal*(bool, TermList)> isRat;
  std::function<Literal*(bool, TermList)> isReal;

};

inline SyntaxSugarGlobals& syntaxSugarGlobals() 
{ return SyntaxSugarGlobals::instance(); }


class TermSugar 
{
  TermList _trm;

public:
  TermSugar(bool foolConst) 
    : _trm(TermList(foolConst ? Term::foolTrue() : Term::foolFalse()))
  { }

  TermSugar(int trm) 
    : _trm(TermList(syntaxSugarGlobals().createNumeral(trm)))
  { }

  TermSugar(TermList trm) 
    : _trm(trm)
  { ASS_REP(!_trm.isEmpty(), _trm);  }

  /** implicit conversion */ 
  operator TermList() const {return _trm;}

  /** explicit conversion */ 
  TermList toTerm() const { return _trm;} 

  static TermSugar createConstant(const char* name, SortSugar s) {
    unsigned f = env.signature->addFunction(name,0);                                                                
    env.signature->getFunction(f)->setType(OperatorType::getFunctionType({}, s.sortId()));
    return TermSugar(TermList(Term::createConstant(f)));                                                          
  }                                                                                                                 
};

class Lit
{
  Literal* _lit;
  bool _selected;
public:
  Lit(Literal* lit) : _lit(lit), _selected(false) {}

  operator Literal*() const 
  { return _lit; }

  bool selected() const 
  { return _selected; }

  friend Lit selected(Lit l) 
  {
    l._selected = true;
    return l;
  }
};

inline TermSugar frac(int a, int b) 
{ return syntaxSugarGlobals().createFraction(a,b); }

inline TermSugar num(int a)
{ return syntaxSugarGlobals().createNumeral(a); }

inline TermSugar fool(bool b)
{ return TermSugar(b); }

////////////////////////// operators to create terms ////////////////////////// 

inline TermSugar operator+(TermSugar lhs, TermSugar rhs)  { return syntaxSugarGlobals().add(lhs, rhs); }  
inline TermSugar operator*(TermSugar lhs, TermSugar rhs)  { return syntaxSugarGlobals().mul(lhs, rhs); }  
inline TermSugar operator/(TermSugar lhs, TermSugar rhs)  { return syntaxSugarGlobals().div(lhs, rhs); }  

#define __IMPL_NUMBER_BIN_FUN(op, result_t)                                                                   \
  inline result_t op(int lhs, TermSugar rhs) { return op(TermSugar(lhs), rhs); }                              \
  inline result_t op(TermSugar lhs, int rhs) { return op(lhs, TermSugar(rhs)); }                              \

__IMPL_NUMBER_BIN_FUN(operator+, TermSugar)
__IMPL_NUMBER_BIN_FUN(operator*, TermSugar)
__IMPL_NUMBER_BIN_FUN(operator/, TermSugar)

#define __BIN_FUNC_QUOTIENT_REMAINDER(X)                                                                      \
  inline TermSugar  quotient##X(TermSugar lhs, TermSugar rhs){ return syntaxSugarGlobals(). quotient##X(lhs, rhs); }   \
  inline TermSugar remainder##X(TermSugar lhs, TermSugar rhs){ return syntaxSugarGlobals().remainder##X(lhs, rhs); }   \
                                                                                                              \
  __IMPL_NUMBER_BIN_FUN( quotient##X, TermSugar)                                                              \
  __IMPL_NUMBER_BIN_FUN(remainder##X, TermSugar)                                                              \

__BIN_FUNC_QUOTIENT_REMAINDER(E)
__BIN_FUNC_QUOTIENT_REMAINDER(T)
__BIN_FUNC_QUOTIENT_REMAINDER(F)

#undef __BIN_FUNC_QUOTIENT_REMAINDER


inline TermSugar operator-(TermSugar x) { return syntaxSugarGlobals().minus(x); }

////////////////////////// operators to create literals ////////////////////////// 


inline Lit operator==(TermSugar lhs, TermSugar rhs) 
{
  SortId sort;
  ALWAYS(SortHelper::tryGetResultSort(lhs, sort) || SortHelper::tryGetResultSort(rhs, sort));
  return Literal::createEquality(true, lhs, rhs, sort);
}


inline Lit operator< (TermSugar lhs, TermSugar rhs) { return syntaxSugarGlobals().less   (true, lhs, rhs); }
inline Lit operator<=(TermSugar lhs, TermSugar rhs) { return syntaxSugarGlobals().leq    (true, lhs, rhs); }
inline Lit operator> (TermSugar lhs, TermSugar rhs) { return syntaxSugarGlobals().greater(true, lhs, rhs); }
inline Lit operator>=(TermSugar lhs, TermSugar rhs) { return syntaxSugarGlobals().geq    (true, lhs, rhs); }

inline Lit isInt (TermSugar trm) { return syntaxSugarGlobals().isInt (true, trm); }
inline Lit isRat (TermSugar trm) { return syntaxSugarGlobals().isRat (true, trm); }
inline Lit isReal(TermSugar trm) { return syntaxSugarGlobals().isReal(true, trm); }

inline Lit operator~(Lit lit) 
{
  Literal* l = lit;
  return Literal::create(l, !l->polarity());
}

inline Lit operator!=(TermSugar lhs, TermSugar rhs) 
{ return ~(lhs == rhs); }

__IMPL_NUMBER_BIN_FUN(operator==, Lit)
__IMPL_NUMBER_BIN_FUN(operator!=, Lit)
__IMPL_NUMBER_BIN_FUN(operator< , Lit)
__IMPL_NUMBER_BIN_FUN(operator<=, Lit)
__IMPL_NUMBER_BIN_FUN(operator> , Lit)
__IMPL_NUMBER_BIN_FUN(operator>=, Lit)


class FuncSugar {
  unsigned _functor;
  unsigned _arity;

public:
  explicit FuncSugar(unsigned functor) 
    : _functor(functor)
    , _arity(env.signature->getFunction(functor)->arity()) {}

  FuncSugar(vstring const& name, Stack<SortSugar> as_, SortSugar result) 
  {
    Stack<SortId> as;
    for (auto a : as_) 
      as.push(a.sortId());

    bool added = false;
    _functor = env.signature->addFunction(name, as.size(), added);
    _arity = as.size();
    if (added)
      env.signature
        ->getFunction(_functor)
        ->setType(OperatorType::getFunctionType(as.size(), as.begin(), result.sortId()));    
  }

  FuncSugar dtor(unsigned i) const {
    CALL("FuncSugar::dtor(unsigned)")
    ASS_L(i, arity())
    ASS (symbol()->termAlgebraCons()) 
    return FuncSugar(
        env.signature->getTermAlgebraConstructor(functor())
          ->destructorFunctor(i));
  }

  auto result()        const { return symbol()->fnType()->result(); }
  auto arg(unsigned i) const { return symbol()->fnType()->arg(i);   }

  template<class... As>
  TermSugar operator()(As... args) const {
    BYPASSING_ALLOCATOR
    Stack<TermList> as { TermSugar(args).toTerm()... };
    return TermList(Term::create(_functor, 
        as.size(), 
        as.begin()));
  }
  unsigned functor() const { return _functor; }
  unsigned arity() const { return _arity; }
  Signature::Symbol* symbol() const { return env.signature->getFunction(functor()); }

  friend std::ostream& operator<<(std::ostream& out, FuncSugar const& self) 
  { return out << self.symbol()->name(); }
};

class ConstSugar : public TermSugar, public FuncSugar
{
public:
  ConstSugar(const char* name, SortSugar s)
    : TermSugar(TermSugar::createConstant(name, s).toTerm())
    , FuncSugar(functor())
  { }
  unsigned functor() const { return this->toTerm().term()->functor(); }
};

class PredSugar {
  unsigned _functor;

public:
  PredSugar(const char* name, Stack<SortSugar> args) 
  {
    BYPASSING_ALLOCATOR
    Stack<SortId> as;
    for (auto a : args) {
      as.push(a.sortId());
    }
    _functor = env.signature->addPredicate(name, as.size());
    env.signature
      ->getPredicate(_functor)
      ->setType(OperatorType::getPredicateType(as.size(), &as[0]));    
  }

  template<class... As>
  Lit operator()(As... args) const {
    Stack<TermList> as { TermSugar(args).toTerm()... };
    return Literal::create(_functor, 
        as.size(), 
        /* polarity */ true, 
        /* commutative */ false, 
        as.begin() );
  }
  unsigned functor() const { return _functor; }
};

inline Clause* clause(std::initializer_list<Lit> ls_) { 
  static Inference testInf = Kernel::NonspecificInference0(UnitInputType::ASSUMPTION, InferenceRule::INPUT); 

  Stack<Lit> ls(ls_);
  std::stable_sort(ls.begin(), ls.end(), [](Lit const& l1, Lit const& l2){ return l1.selected() > l2.selected(); });
  auto nSelected = iterTraits(ls.iterFifo())
    .findPosition([](Lit const& l) 
        { return !l.selected(); })
    .unwrapOrElse( [&]() {return ls.size(); });

  Clause& out = *new(ls.size()) Clause(ls.size(), testInf); 

  auto l = ls.begin(); 
  for (unsigned i = 0; i < ls.size(); i++) { 
    Literal* lit = *l;
    out[i] = lit; 
    l++; 
  }
  out.setSelected(nSelected);
  return &out; 
}

inline Stack<Clause*> clauses(std::initializer_list<std::initializer_list<Lit>> cls) { 
  auto out = Stack<Clause*>();
  for (auto cl : cls) {
    out.push(clause(cl));
  }
  return out;
}

inline void createTermAlgebra(SortSugar sort, initializer_list<FuncSugar> fs) {

  using namespace Shell;

  Stack<FuncSugar> funcs = fs;
  Stack<TermAlgebraConstructor*> cons;

  for (auto f : funcs) {
    env.signature->getFunction(f.functor())
      ->markTermAlgebraCons();
    auto dtor = [&](unsigned i) {
      vstringstream name;
      name << f << "@" << i;
      auto d = FuncSugar(name.str(), { f.result() }, f.arg(i));
      env.signature->getFunction(d.functor())
        ->markTermAlgebraDest();
      return d;
    };

    Array<unsigned> dtors(f.arity()); 
    for (unsigned i = 0; i < f.arity(); i++) {
      dtors[i] = dtor(i).functor();
    }

    cons.push(new TermAlgebraConstructor(f.functor(), dtors));
  }
  auto ta = new TermAlgebra(sort.sortId(), cons.size(), cons.begin());
  env.signature->addTermAlgebra(ta);
}

#endif // __TEST__SYNTAX_SUGAR__H__
