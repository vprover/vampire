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

#include "Api/FormulaBuilder.hpp"
#include "Api/Problem.hpp"
#include "Lib/Coproduct.hpp"
#include "Lib/Map.hpp"
#include "Kernel/Clause.hpp"

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
      Map<unsigned, unsigned> _self;
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

  std::ostream& prettyPrint(std::ostream& out) const
  { return out << _self; }

  template<class U>
  friend Pretty<U> pretty(const U& t);
};

template<class U>
Pretty<U> pretty(const U& t) 
{ return Pretty<U>(t); }


template<class U>
std::ostream& operator<<(std::ostream& out, const Pretty<U>& self)
{  return self.prettyPrint(out); }


template<class... As>
class Pretty<Lib::Coproduct<As...>> 
{
  Lib::Coproduct<As...> const& _self;

public:
  Pretty(Lib::Coproduct<As...> const& self) : _self(self) { }

  std::ostream& prettyPrint(std::ostream& out) const
  { return _self.apply([&](auto const& a) -> std::ostream& { return out << pretty(a); }); }
};


template<class A>
class Pretty<A*> {
  A* const& _self;

public:
  Pretty(A* const& self) : _self(self) {}

  std::ostream& prettyPrint(std::ostream& out) const
  { return _self == nullptr ? out << "null" : out << pretty(*_self); }
};


template<class A>
class Pretty<Stack<A>> {
  Stack<A> const& _self;

public:
  Pretty(Stack<A> const& self) : _self(self) {}

  std::ostream& prettyPrint(std::ostream& out) const
  {
    auto iter = _self.iterFifo();
    out << "[ ";
    if (iter.hasNext()) {
      out << pretty(iter.next());
      while (iter.hasNext()) {
        out << ", " << pretty(iter.next());
      }
    }
    out << " ]";
    return out;
  }
};


template<class A>
class Pretty<Option<A>> {
  Option<A> const& _self;

public:
  Pretty(Option<A> const& self) : _self(self) {}

  std::ostream& prettyPrint(std::ostream& out) const
  { return _self.isSome() ? out << pretty(_self.unwrap()) : out << "none"; }
};

template<class A>
class Pretty<unique_ptr<A>> {
  unique_ptr<A> const& _self;

public:
  Pretty(unique_ptr<A> const& self) : _self(self) {}

  std::ostream& prettyPrint(std::ostream& out) const
  { return out << pretty(*_self); }
};

template<class A, class B>
class Pretty<pair<A,B>> {
  pair<A,B> const& _self;

public:
  Pretty(pair<A,B> const& self) : _self(self) {}

  std::ostream& prettyPrint(std::ostream& out) const
  { return out << pretty(_self.first) << " : " << pretty(_self.second); }
};

template<class L1, class L2, class Eq>
bool TestUtils::permEq(L1& lhs, L2& rhs, Eq elemEq)
{
  const auto n = lhs.size();
  if (n != rhs.size()) return false;
  DArray<unsigned> perm(n);
  DArray<DHSet<unsigned>> bl(n);
  DArray<unsigned> c(n);
  DArray<bool> b(n);
  for (unsigned i = 0; i < n; i++) {
    bl[i].reset();
    perm[i] = i;
    c[i] = 0;
    b[i] = false;
  }
  unsigned bad = 0;
  auto checkPerm = [] (DArray<unsigned>& perm, DArray<DHSet<unsigned>>& bl, DArray<bool>& b, unsigned& bad, Eq& elemEq, L1& lhs, L2& rhs) {
    for (unsigned i = 0; i < perm.size(); i++) {
      if (!elemEq(lhs[i], rhs[perm[i]])) {
        bl[i].insert(perm[i]);
        bad++;
        b[i] = true;
        return false;
      }
    }
    return true;
  };
  if (checkPerm(perm, bl, b, bad, elemEq, lhs, rhs)) {
    return true;
  }
  auto maintainState = [](DArray<unsigned>& perm, DArray<DHSet<unsigned>>& bl, DArray<bool>& b, unsigned& bad, unsigned i) {
    if (bl[i].find(perm[i]) != b[i]) {
      b[i] ? --bad : ++bad;
      b[i] ^= 1;
    }
  };
  unsigned i = 1;
  while (i < n) {
    if (c[i] < i) {
      if (i % 2 == 0) {
        swap(perm[0], perm[i]);
        maintainState(perm, bl, b, bad, 0);
      } else {
        swap(perm[c[i]], perm[i]);
        maintainState(perm, bl, b, bad, c[i]);
      }
      maintainState(perm, bl, b, bad, i);
      if (!bad && checkPerm(perm, bl, b, bad, elemEq, lhs, rhs)) {
        return true;
      }
      c[i]++;
      i = 1;
    } else {
      c[i] = 0;
      i++;
    }
  }

  return false;
}

inline void setOptions(std::initializer_list<pair<vstring,vstring>> opts) {
  for (const auto& kv : opts) {
    env.options->set(kv.first, kv.second);
  }
}

#define SET_OPTIONS(...) Test::setOptions(__VA_ARGS__);

} // namespace Test

#endif // __TestUtils__
