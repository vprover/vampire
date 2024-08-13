/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file TestUtils.hpp
 * Defines class TestUtils.
 */

#ifndef __TestUtils__
#define __TestUtils__

#include "Forwards.hpp"
#include "Kernel/Theory.hpp"
#include "Kernel/Signature.hpp"
#include "Lib/Environment.hpp"

#include "Lib/Coproduct.hpp"
#include "Lib/Map.hpp"
#include "Kernel/Clause.hpp"
#include <memory>

namespace Test {
class TestUtils {

public:
  /** 
   * Tests whether two terms are equal modulo associativity and commutativity.
   * Whether a method is assoc and commut is checked with `TestUtils::isAC(..)`
   *
   * !!! exponential runtime !!!
   */
  static bool eqModAC(Kernel::TermList lhs, Kernel::TermList rhs);

  /** 
   * Tests whether two clauses are equal. All permutations of the clauses are tested. Variable renamings are 
   * not taken into account (i.e.: { p(x) } is NOT equal to { p(y) } for this function).
   *
   * !!! exponential runtime !!!
   */
  static bool eqModAC(const Kernel::Clause* lhs, const Kernel::Clause* rhs);
  static bool eqModAC(Kernel::Literal* lhs, Kernel::Literal* rhs);

  // /** 
  //  * Tests whether two clauses are equal. All permutations of the clauses are tested. Variable renamings are 
  //  * taken into account (i.e.: { p(x) } IS equal to { p(y) } for this function).
  //  *
  //  * !!! exponential runtime !!!
  //  */
  // static bool eqModACVar(const Kernel::Clause* lhs, const Kernel::Clause* rhs);

  /**
   * The ... are len of integers, positive -- positive polarity, negative -- negative polarity.
   */
  static SAT::SATClause* buildSATClause(unsigned len,...);



  /**
   * Tests whether there is a permutation pi s.t. pi(lhs) == rhs, where elements are compared by
   * elemEq(l,r)
   * `List` must provide methods
   *    - `elem_type operator[](unsigned)`
   *    - `unsigned size()`
   * `Eq`   must provide methods
   *    - `bool operator(const elem_type&, const elem_type&)`
   */
  template<class L1, class L2, class Eq>
  static bool permEq(L1& lhs, L2& rhs, Eq elemEq);

private:

  struct RectMap
  {
    class Inner {
      unsigned cnt = 0;
      Lib::Map<unsigned, unsigned> _self;
    public:
      unsigned get(unsigned var) 
      { return _self.getOrInit(std::move(var), [&](){ return cnt++; }); }
    };
    Inner l;
    Inner r;
  };


  // static bool eqModACVar(const Kernel::Clause* lhs, const Kernel::Clause* rhs, RectMap& r);
  // static bool eqModACVar(Kernel::Literal* lhs, Kernel::Literal* rhs, RectMap& r);
  // static bool eqModACVar(Kernel::TermList lhs, Kernel::TermList rhs, RectMap& r);
  template<class Comparisons>
  static bool eqModAC_(Kernel::TermList lhs, Kernel::TermList rhs, Comparisons c);

  /** returns whether the function f is associative and commutative */
  static bool isAC(Kernel::Theory::Interpretation f);
  static bool isAC(Kernel::Term* f);
};

template<class A>
struct PrettyPrinter {
  void operator()(std::ostream& out, A const& self)
  { out << self; }
};

/** 
 * Newtype for pretty-printing objects. 
 *
 * Usage: 
 * std::cout << pretty(obj) << std::endl;
 */
template<class T>
class Pretty {
  const T& _self;
public:
  Pretty(const T& t) : _self(t) { }

  template<class U>
  friend Pretty<U> pretty(const U& t);

  // template<class U>
  friend std::ostream& operator<<(std::ostream& out, const Pretty<T>& self)
  { PrettyPrinter<T>{}(out, self._self); return out; }
};

template<class U>
Pretty<U> pretty(const U& t) 
{ return Pretty<U>(t); }


template<class... As>
struct PrettyPrinter<Lib::Coproduct<As...>> {
  void operator()(std::ostream& out, Lib::Coproduct<As...> const& self)
  { self.apply([&](auto const& a) -> std::ostream& { return out << pretty(a); }); }
};

template<class A>
struct PrettyPrinter<A*> {
  void operator()(std::ostream& out, A* const& self)
  { if (self == nullptr) out << "nullptr"; else out << pretty(*self); }
};

template<class A>
struct PrettyPrinter<Lib::Stack<A>> {
  void operator()(std::ostream& out, Lib::Stack<A> const& self)
  {
    auto iter = self.iterFifo();
    out << "[ ";
    if (iter.hasNext()) {
      out << pretty(iter.next());
      while (iter.hasNext()) {
        out << ", " << pretty(iter.next());
      }
    }
    out << " ]";
  }
};

template<class A>
struct PrettyPrinter<Lib::Option<A>> {
  void operator()(std::ostream& out, Lib::Option<A> const& self)
  { self.isSome() ? out << pretty(self.unwrap()) : out << "none"; }
};

template<class A>
struct PrettyPrinter<std::unique_ptr<A>> {
  void operator()(std::ostream& out, std::unique_ptr<A> const& self)
  { out << pretty(*self); }
};

template<class A, class B>
struct PrettyPrinter<std::pair<A,B>> {
  void operator()(std::ostream& out, std::pair<A,B> const& self)
  { out << pretty(self.first) << " : " << pretty(self.second); }
};

template<>
struct PrettyPrinter<Kernel::Clause> 
{ 
  void operator()(std::ostream& out, Kernel::Clause const& self)
  { 
    auto iter = self.iterLits();
    if (iter.hasNext()) {
      out << pretty(*iter.next());
      while(iter.hasNext()) {
        out << " \\/ " << pretty(*iter.next());
      }
    } else {
      out << "bot";
    }
  }
};

inline std::ostream& printOp(std::ostream& out, const Kernel::Term* t, const char* op) {
  auto l = *t->nthArgument(0);
  auto r = *t->nthArgument(1);
  return out << "(" << pretty(l) << " " << op << " " << pretty(r) << ")";
}

template<>
struct PrettyPrinter<Kernel::Literal> 
{ 
  void operator()(std::ostream& out, Kernel::Literal const& lit)
  {
    using namespace std;
    using namespace Kernel;
    auto print = [&]() -> ostream& {

      auto func = lit.functor();
      if(theory->isInterpretedPredicate(func)) {
        switch(theory->interpretPredicate(func)) {
#define NUM_CASE(oper) \
          case Kernel::Theory::INT_  ## oper: \
          case Kernel::Theory::REAL_ ## oper: \
          case Kernel::Theory::RAT_  ## oper

          NUM_CASE(LESS_EQUAL):
            return printOp(out, &lit, "<=");
          case Kernel::Theory::EQUAL:
            return printOp(out, &lit, "=");
          default: 
          {
          }
#undef NUM_CASE
        }
      }
      Signature::Symbol* sym = Lib::env.signature->getPredicate(func);
      out << sym->name();
      if (sym->arity() > 0) {
        out << "(" << pretty(*lit.nthArgument(0));
        for (unsigned i = 1; i < sym->arity(); i++) {
          out << ", " << pretty(*lit.nthArgument(i));
        }
        out << ")";
      }
      return out;
    };


    if (!lit.polarity()) {
      out << "~(";
    }
    print();
    if (!lit.polarity()) {
      out << ")";
    }
  }
};
template<>
struct PrettyPrinter<Kernel::TermList> 
{ 
  void operator()(std::ostream& out, Kernel::TermList const& t)
  {
    using namespace Kernel;

    if (t.isVar()) {
      out << "X" << t.var();
    } else {
      auto term = t.term();
      auto func = term->functor();
      if (theory->isInterpretedFunction(func)) {
        switch(theory->interpretFunction(func)) {
#define NUM_CASE(oper) \
          case Kernel::Theory::INT_  ## oper: \
          case Kernel::Theory::REAL_ ## oper: \
          case Kernel::Theory::RAT_  ## oper

          NUM_CASE(PLUS):     
            printOp(out, term, "+"); 
            return;
          NUM_CASE(MULTIPLY):
            printOp(out, term, "*");
            return;
          // case Kernel::Theory::EQUAL:
          //   return printOp("=")
          default: {}
#undef NUM_CASE
        }
      }

      Signature::Symbol* sym = Lib::env.signature->getFunction(func);
      out << sym->name();
      if (sym->arity() > 0) {
        out << "(" << pretty(*term->nthArgument(0));
        for (unsigned i = 1; i < sym->arity(); i++) {
          out << ", " << pretty(*term->nthArgument(i));
        }
        out << ")";
      }
    }
  }
};

// Helper function for permEq -- checks whether lhs is a permutation of
// rhs via initial permutation perm with elements [0,idx) fixed.
template<class L1, class L2, class Eq>
bool __permEq(L1& lhs, L2& rhs, Eq elemEq, Lib::DArray<unsigned>& perm, unsigned idx) {
  auto checkPerm = [] (L1& lhs, L2& rhs, Eq elemEq, Lib::DArray<unsigned>& perm, unsigned idx) {
    ASS_EQ(lhs.size(), perm.size());
    ASS_EQ(rhs.size(), perm.size());

    for (unsigned i = idx; i < perm.size(); i++) {
      if (!elemEq(lhs[i], rhs[perm[i]])) {
        return false;
      }
    }
    return true;
  };
  // These are elements fixed in the permutation, so check
  // them only once and do not recurse if one of them is false.
  for (unsigned i = 0; i < idx; i++) {
    if (!elemEq(lhs[i], rhs[perm[i]])) {
      return false;
    }
  }
  if (checkPerm(lhs, rhs, elemEq, perm, idx)) {
    return true;
  }
  for (unsigned i = idx; i < perm.size(); i++) {
    using std::swap;//ADL
    swap(perm[i], perm[idx]);

    if (__permEq(lhs,rhs, elemEq, perm, idx+1)) return true;

    swap(perm[i], perm[idx]);
  }

  return false;
}

template<class L1, class L2, class Eq>
bool TestUtils::permEq(L1& lhs, L2& rhs, Eq elemEq)
{
  if (lhs.size() != rhs.size()) return false;
  Lib::DArray<unsigned> perm(lhs.size());
  for (unsigned i = 0; i < lhs.size(); i++) {
    perm[i] = i;
  }
  return __permEq(lhs, rhs, elemEq, perm, 0);
}

} // namespace Test

#endif // __TestUtils__
