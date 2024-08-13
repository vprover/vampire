/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __LIB__BOTTOM_UP_EVALUATION_HPP__
#define __LIB__BOTTOM_UP_EVALUATION_HPP__

#define DEBUG(...) // DBG(__VA_ARGS__)

/**
 * @file Kernel/BottomUpEvaluation.hpp
 *
 * This file contains mainly the function Lib::evaluateBottomUp, that can be used to evaluate an arbitrary
 * acyclic graph structure bottom up. It uses iteration instead of recursion and can be equipped with memoization structures
 * found in Lib::Memo.
 *
 * \see UnitTests/tBottomUpEvaluation.cpp
 * \see Lib::evaluateBottomUp
 */

#include "Lib/Stack.hpp"
#include "Lib/Recycled.hpp"
#include "Lib/Option.hpp"
#include "Lib/TypeList.hpp"
#include <utility>

namespace Lib {
  using EmptyContext = std::tuple<>;

namespace Memo {

  /** a mocked memoization that does not store any results */
  template<class Arg, class Result>
  struct None
  {
    Lib::Option<Result> get(Arg const&)
    { return Lib::Option<Result>(); }

    template<class Init> Result getOrInit(Arg const& orig, Init init)
    { return init(); }
  };

  /** a memoization realized as a hashmap */
  template<class Arg, class Result, class Hash = DefaultHash>
  class Hashed
  {
    Lib::Map<Arg, Result, Hash> _memo;

  public:
    Hashed() : _memo(decltype(_memo)()) {}

    template<class Init> Result getOrInit(Arg const& orig, Init init)
    { return _memo.getOrInit(Arg(orig), init); }

    Lib::Option<Result> get(const Arg& orig)
    { return _memo.tryGet(orig).toOwned(); }
  };

} // namespace Memo

/**
 * An iterator over the children of a node in a Directed Acyclic Graph (DAG).
 * The DAG is a structure to be evaluate bottom up using evaluateBottomUp.
 * A template-specialization of this struct with the methods like in this template
 * must be implemented for a class in order to bottom-up evaluatable.
 */
template<class A>
struct BottomUpChildIter
{
  /** a context argument that will be passed to every function called to the iterator. 
   *
   * An example for such a term are `TermSpec`s in Substitution trees which have a RobSubstution as a context
   * and variables are automatically dereferenced according to the substitution.
   * Concretely think for example of doing arithmetic simplifications on the term f(X0) the context { X0 -> 1 + 2 }.
   * Passing `Context = RobSubstition*` we can evaluate it straight to `f(3)`. 
   *
   * Note that every type `A` must define exactly one Context. 
   * If you want do use multiple different contexts you have to newtype A.
   * */
  using Context = EmptyContext;

  /** constructs an iterator over the children of the current node */
  BottomUpChildIter(A a, Context c);

  /** returns the node this iterator was constructed with */
  A self(Context c);

  /** returns the next child of the node this this object was constructed with */
  A next(Context c);

  /** returns the next child of the current node in the structure to be traversed */
  bool hasNext(Context c);

  /** returns how many children this node has */
  unsigned nChildren(Context c);
};

template<class A> BottomUpChildIter<A> bottomUpChildIter(A a)
{ return BottomUpChildIter<A>(a); }

namespace TL = Lib::TypeList;

// TODO move MapTuple to its own file
template<unsigned I, class Indexed>
struct MapTupleElem;

template<unsigned I, unsigned J, class A>
struct MapTupleElem<I, TL::Indexed<J, A>>
{
  template<class Tup, class F>
  inline static auto apply(Tup& bs, F& f) -> A
  { return std::get<J>(bs); }
};

template<unsigned I, class A>
struct MapTupleElem<I, TL::Indexed<I, A>>
{
  template<class Tup, class F>
  inline static auto apply(Tup& bs, F& f) -> decltype(auto) 
  { return std::move(f)(std::get<I>(bs)); }
};

template<unsigned N, class F, class Tup, class... Indexed>
auto __mapTupleElem(Tup tup, F f, TL::List<Indexed...>) -> decltype(auto) {
  return std::tuple<
    decltype(MapTupleElem<N, Indexed>::apply(tup, f))...
    >(MapTupleElem<N, Indexed>::apply(tup, f)...);
}

template<unsigned N, class F, class... As> 
auto mapTupleElem(std::tuple<As...> tup, F f) -> decltype(auto) 
{ return __mapTupleElem<N>(std::move(tup), f, TL::WithIndices<TL::List<As...>>{}); }

template<unsigned N, class B, class... As> 
auto replaceTupleElem(std::tuple<As...> tup, B b) -> decltype(auto) 
{ return mapTupleElem<N>(std::move(tup), [&](auto) -> B { return move_if_value<B>(b); }); }

template<class Type>
struct ReturnNone {
  template<class... As>
  constexpr Lib::Option<Type> operator()(As...) const { return Lib::Option<Type>(); }
};

template<class Arg, class Result>
using NoMemo = Memo::None<Arg, Result>;

/**
 * this macro defines all the fields for BottomUpEvaluation class. 
 * This class uses the builder-pattern, which is implemented using macros for all the fields
 * regiestered below. 
 * For how to use `BottomUpEvaluation` have a look at the file `tBottomUpEvaluation`, and the 
 * documentation of the function `apply`
 */
#define FOR_FIELD(MACRO)                                                                  \
  MACRO(0, Function , function      , (std::tuple<>())           )                        \
  MACRO(1, EvNonRec , evNonRec      , (ReturnNone<Result>{})     )                        \
  MACRO(2, Memo     , memo          , (NoMemo<Arg, Result>()))                            \
  MACRO(3, Context  , context       , (EmptyContext())           )                        \
  /*    ^  ^^^^^^^^^  ^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^----> default value */
  /*    |      |         +--------------------------------------------> field name */
  /*    |      +------------------------------------------------------> type param name */
  /*    +-------------------------------------------------------------> index */

template< class Arg
        , class Result  
#                                       define foreach(idx, Type, name, defaultVal)       \
        , class Type = decltype(defaultVal) 
                                        FOR_FIELD(foreach)
#                                       undef foreach
  >
class BottomUpEvaluation {

  template<class A, class R
#                                       define foreach(idx, Type, name, defaultVal)       \
  , class Type ## _
                                        FOR_FIELD(foreach)
#                                       undef foreach
                                        > 
 friend class BottomUpEvaluation;

  std::tuple<> _dummy;
#                                       define foreach(idx, Type, name, defaultVal)       \
  Type _ ## name;
                                        FOR_FIELD(foreach)
#                                       undef foreach

  BottomUpEvaluation(
      std::tuple<
#                                       define foreach(idx, Type, name, defaultVal)       \
                Type,
                                        FOR_FIELD(foreach)
#                                       undef foreach
                std::tuple<>> elems)
    : _dummy()

#                                       define foreach(idx, Type, name, defaultVal)       \
    , _ ## name(std::get<idx>(elems))
                                        FOR_FIELD(foreach)
#                                       undef foreach
  { }

  template<
#                                       define foreach(idx, Type, name, defaultVal)       \
                class Type ## _,
                                        FOR_FIELD(foreach)
#                                       undef foreach
                class... Dummies
    >

  static auto fromTuple(
      std::tuple<
#                                       define foreach(idx, Type, name, defaultVal)       \
        Type ## _,
                                        FOR_FIELD(foreach)
#                                       undef foreach
        std::tuple<>
      > tup)
  { return BottomUpEvaluation< Arg
                             , Result
#                                       define foreach(idx, Type, name, defaultVal)       \
                             , Type ## _
                                        FOR_FIELD(foreach)
#                                       undef foreach
                             >(std::move(tup)); }

  auto intoTuple() &&
  { return std::tuple<
#                                       define foreach(idx, Type, name, defaultVal)       \
             Type,
                                        FOR_FIELD(foreach)
#                                       undef foreach
             std::tuple<>
    >(
#                                       define foreach(idx, Type, name, defaultVal)       \
             move_if_value<Type>(_ ## name),
                                        FOR_FIELD(foreach)
#                                       undef foreach
             std::make_tuple()); }

public:
  BottomUpEvaluation() 
    : BottomUpEvaluation(
        std::tuple<
#                                       define foreach(idx, Type, name, defaultVal)       \
             Type,
                                        FOR_FIELD(foreach)
#                                       undef foreach
             std::tuple<>
    >(
#                                       define foreach(idx, Type, name, defaultVal)       \
             defaultVal,
                                        FOR_FIELD(foreach)
#                                       undef foreach
             std::make_tuple()))
  {}


#                                       define foreach(idx, Type, name, defaultVal)       \
  template<class New>                                                                     \
  auto name(New val) &&                                                                   \
  { return fromTuple(replaceTupleElem<idx, New>(std::move(*this).intoTuple(), move_if_value<New>(val))); }\
                                                                                          \
  Type& name() { return _ ## name; }                                                      \


                                        FOR_FIELD(foreach)
#                                       undef foreach


  /**
   * Evaluates a term-like datastructure (i.e.: a Directed Acyclic Graph (DAG)) bottom up without using 
   * recursion, but an explicit Stack.
   *
   * The term to be evaluated will be traversed using a BottomUpChildIter<Arg>, which needs to be 
   * specialized for whatever structure you want to evalute. Implementations for `Kernel::TermList`, and 
   * `Kernel::PolyNf` are provided below and for `z3::expr` is provided in `Z3Interfacing`. 
   *
   * It is to be used as follows (this example computes the weight of a term):
   * ```
   *  Memo::Hashed<TermList, size_t> memo;
   *  ...
   *  return BottomUpEvaluation<TermList, size_t>()
   *                         // ^^^^^^^^  ^^^^^^--> result type
   *                         //    +--> type to evaluate
   *    // sets the function that will be used to evalute recursively
   *    .function(
   *      [](auto const& orig, size_t* sizes) -> size_t
   *         //          ^^^^  ^^^^^-> results of evaluating its arguments recursively
   *         //           +-> original term that needs to be evaluate
   *      { return !orig.isTerm() ? 1 
   *                              : (1 + range(0, orig.nAllArgs())
   *                                       .map([&](auto i) { return sizes[i]; })
   *                                       .sum()); })
   *
   *    // (optional)
   *    // this can be set to define for which terms recursing can be skipped. 
   *    // In this case we do it for shared terms if the function returns a value (non-empty Option) 
   *    // the evalution does not recurse but just use the result. If the returned option is empty 
   *    // the term is recursively evaluated as usual.
   *    .evNonRec([](auto& t) { return t.shared() ? Lib::Option<size_t>(t.weight) : Lib::Option<size_t>()); })
   *
   *    // (optional)
   *    // a memo can be used cache evaluated sub result. We need to explicitly specify to pass it as 
   *    // reference as otherwise the memo is copied each time this function is called and the cached
   *    // values will not be shared among different evaluation calls
   *    .memo<decltype(memo)&>(memo)
   *
   *    // (optional)
   *    // some term sutructures (like AutoDerefTermSpec in RobSubstition) need a context to be traversed
   *    // with BottomUpChildIter. this context needs to be passed here.
   *    // .context(AutoDerefTermSpec::Context { .subs = this, })
   *
   *    // applys the evaluation
   *    .apply(someTerm)
   *    ;
   * ```
   */
  Result apply(Arg const& toEval) 
  {
    /* recursion state. Contains a stack of items that are being recursed on. */
    Lib::Recycled<Lib::Stack<BottomUpChildIter<Arg>>> recState;
    Lib::Recycled<Lib::Stack<Result>> recResults;

    recState->push(BottomUpChildIter<Arg>(toEval, _context));

    while (!recState->isEmpty()) {
      if (recState->top().hasNext(_context)) {
        Arg t = recState->top().next(_context);

        Lib::Option<Result> nonRec = _evNonRec(t);
        if (nonRec) {
          recResults->push(move_if_value<Result>(*nonRec));

        } else {
          Lib::Option<Result> cached = _memo.get(t);
          if (cached.isSome()) {
            recResults->push(std::move(cached).unwrap());
          } else {
            recState->push(BottomUpChildIter<Arg>(t, _context));
          }

        }

      } else {

        BottomUpChildIter<Arg> orig = recState->pop();

        Result* argLst = orig.nChildren(_context) == 0 
          ? nullptr 
          : static_cast<Result*>(&((*recResults)[recResults->size() - orig.nChildren(_context)]));

        Result eval = _memo.getOrInit(orig.self(), 
                        [&](){ return _function(orig.self(), argLst); });

        DEBUG("evaluated: ", orig.self(), " -> ", eval);
        recResults->pop(orig.nChildren(_context));
        recResults->push(std::move(eval));
      }
    }
    ASS(recState->isEmpty())


    ASS(recResults->size() == 1);
    auto result = recResults->pop();
    DEBUG("eval result: ", toEval, " -> ", result);
    return result;
  }
};


}

#include "Kernel/Term.hpp"

namespace Lib {
// specialisation for TermList
// iterate up through TermLists, ignoring sort arguments
template<>
struct BottomUpChildIter<Kernel::TermList>
{
  Kernel::TermList _self;
  unsigned _idx;

  BottomUpChildIter(Kernel::TermList self, EmptyContext = EmptyContext()) : _self(self), _idx(0)
  { }

  Kernel::TermList next(EmptyContext = EmptyContext())
  {
    ASS(hasNext());
    return _self.term()->termArg(_idx++);
  }

  bool hasNext(EmptyContext = EmptyContext()) const
  { return _self.isTerm() && _idx < _self.term()->numTermArguments(); }

  unsigned nChildren(EmptyContext = EmptyContext()) const
  { return _self.isVar() ? 0 : _self.term()->numTermArguments(); }

  Kernel::TermList self(EmptyContext = EmptyContext()) const
  { return _self; }
};
}

#include "TypedTermList.hpp"

namespace Lib {
// specialisation for TypedTermList
template<>
struct BottomUpChildIter<Kernel::TypedTermList>
{
  Kernel::TypedTermList _self;
  unsigned      _idx;

  BottomUpChildIter(Kernel::TypedTermList self, EmptyContext = EmptyContext()) : _self(self), _idx(0)
  {}

  Kernel::TypedTermList next(int);
  Kernel::TypedTermList next(EmptyContext = EmptyContext())
  {
    ASS(hasNext());
    auto cur = self().term();
    auto next = cur->termArg(_idx);
    auto sort = Kernel::SortHelper::getTermArgSort(cur, _idx);
    ASS_NEQ(sort, Kernel::AtomicSort::superSort())
    _idx++;
    return Kernel::TypedTermList(next, sort);
  }

  bool hasNext(EmptyContext = EmptyContext()) const
  { return _self.isTerm() && _idx < _self.term()->numTermArguments(); }

  unsigned nChildren(EmptyContext = EmptyContext()) const
  { return _self.isVar() ? 0 : _self.term()->numTermArguments(); }

  Kernel::TypedTermList self(EmptyContext = EmptyContext()) const
  { return _self; }
};

template<class EvalFn, class Memo>
Kernel::Literal* evaluateLiteralBottomUp(Kernel::Literal* const& lit, EvalFn evaluateStep, Memo& memo)
{
  using namespace Kernel;
  Lib::Recycled<Lib::Stack<TermList>> args;
  for (unsigned i = 0; i < lit->arity(); i++) {
    args->push(
        BottomUpEvaluation<typename EvalFn::Arg, typename EvalFn::Result>()
          .function(evaluateStep)
          .memo(memo)
          .apply(TypedTermList(*lit->nthArgument(i), SortHelper::getArgSort(lit, i))));
  }
  return Literal::create(lit, args->begin());
}


template<class EvalFn>
Kernel::Literal* evaluateLiteralBottomUp(Kernel::Literal* const& lit, EvalFn evaluateStep)
{
  using namespace Memo;
  auto memo = None<typename EvalFn::Arg, typename EvalFn::Result>();
  return evaluateLiteralBottomUp(lit, evaluateStep, memo);
}

} // namespace Lib

#include "Polynomial.hpp"

namespace Lib {
// specialisation for PolyNf
template<>
struct BottomUpChildIter<Kernel::PolyNf>
{
  struct PolynomialBottomUpChildIter
  {
    Kernel::AnyPoly _self;
    unsigned _idx1;
    unsigned _idx2;
    unsigned _nChildren;

    PolynomialBottomUpChildIter(Kernel::AnyPoly self) : _self(self), _idx1(0), _idx2(0), _nChildren(0)
    {
      while (_idx1 < _self.nSummands() && _self.nFactors(_idx1) == 0) {
        _idx1++;
      }
      for (unsigned i = 0; i < _self.nSummands(); i++) {
        _nChildren += self.nFactors(i);
      }
    }

    bool hasNext() const
    { return _idx1 < _self.nSummands(); }

    Kernel::PolyNf next()
    {
      auto out = _self.termAt(_idx1, _idx2++);
      if (_idx2 >= _self.nFactors(_idx1)) {
        _idx1++;
        while (_idx1 < _self.nSummands() && _self.nFactors(_idx1) == 0) {
          _idx1++;
        }
        _idx2 = 0;
      }
      return out;
    }

    unsigned nChildren() const
    { return _nChildren; }

    friend std::ostream& operator<<(std::ostream& out, PolynomialBottomUpChildIter const& self)
    { return out << self._self << "@(" << self._idx1 << ", " << self._idx2 << ")"; }
  };

  struct FuncTermBottomUpChildIter
  {

    Lib::Perfect<Kernel::FuncTerm> _self;
    unsigned _idx;

    FuncTermBottomUpChildIter(Lib::Perfect<Kernel::FuncTerm> self) : _self(self), _idx(0) {}

    bool hasNext() const
    { return _idx < _self->numTermArguments(); }

    Kernel::PolyNf next()
    { return _self->arg(_idx++); }

    unsigned nChildren() const
    { return _self->numTermArguments(); }

    friend std::ostream& operator<<(std::ostream& out, FuncTermBottomUpChildIter const& self)
    { return out << self._self << "@" << self._idx; }
  };


  struct VariableBottomUpChildIter
  {
    Kernel::Variable _self;
    VariableBottomUpChildIter(Kernel::Variable self) : _self(self) {}

    bool hasNext() const
    { return false; }

    Kernel::PolyNf next()
    { ASSERTION_VIOLATION }

    unsigned nChildren() const
    { return 0; }

    friend std::ostream& operator<<(std::ostream& out, VariableBottomUpChildIter const& self)
    { return out << self._self; }
  };

  using Inner = Lib::Coproduct<FuncTermBottomUpChildIter, VariableBottomUpChildIter, PolynomialBottomUpChildIter>;
  Inner _self;

  BottomUpChildIter(Kernel::PolyNf self, EmptyContext = EmptyContext()) : _self(self.match(
        [&](Lib::Perfect<Kernel::FuncTerm> self) { return Inner(FuncTermBottomUpChildIter( self ));            },
        [&](Kernel::Variable                  self) { return Inner(VariableBottomUpChildIter( self ));            },
        [&](Kernel::AnyPoly           self) { return Inner(PolynomialBottomUpChildIter(std::move(self))); }
      ))
  {}

  Kernel::PolyNf next(EmptyContext = EmptyContext())
  { ALWAYS(hasNext()); return _self.apply([](auto& x) -> Kernel::PolyNf { return x.next(); }); }

  bool hasNext(EmptyContext = EmptyContext()) const
  { return _self.apply([](auto& x) { return x.hasNext(); }); }

  unsigned nChildren(EmptyContext = EmptyContext()) const
  { return _self.apply([](auto& x) { return x.nChildren(); }); }

  Kernel::PolyNf self(EmptyContext = EmptyContext()) const
  { return _self.apply([](auto& x) { return Kernel::PolyNf(x._self); }); }

  friend std::ostream& operator<<(std::ostream& out, BottomUpChildIter const& self)
  { return out << self._self; }
};

} // namespace Lib

#undef DEBUG
#endif // __LIB__BOTTOM_UP_EVALUATION_HPP__

