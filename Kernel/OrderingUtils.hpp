/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __OrderingUtils__
#define __OrderingUtils__

#include "Debug/Assertion.hpp"
#include "Lib/Option.hpp"
#include "Kernel/Theory.hpp"
#include "Kernel/Ordering.hpp"
#include "Lib/STL.hpp"
#include "Lib/Output.hpp"

namespace Kernel {
  using namespace Lib;

  template<class T>
  class MultiSet {
    Stack<std::tuple<T, IntegerConstantType>> _elems;
  public:
    void integrity() const {
#if VDEBUG
      ASS(std::is_sorted(_elems.begin(), _elems.end(), [](auto l, auto r) { return std::get<0>(l) < std::get<0>(r); }))
      for (auto e : _elems) {
        ASS_G(std::get<1>(e), IntegerConstantType(0))
      }
#endif
    }

    MultiSet() : _elems() {}
    MultiSet(MultiSet&&) = default;
    MultiSet& operator=(MultiSet&&) = default;
    MultiSet(T t1, T t2) : MultiSet() {
      init(std::move(t1), std::move(t2));
    }

    Stack<std::tuple<T, IntegerConstantType>>& raw() { return _elems; }

    template<class Iter>
    static MultiSet fromIterator(Iter i) 
    { 
      auto stack = i.template collect<Stack>();
      return MultiSet (std::move(stack)); 
    }

    auto iter()  const
    { return iterTraits(_elems.iterFifo()); }

    auto iter() 
    { return iterTraits(_elems.iterFifo()); }

    auto iterDiff(MultiSet const& other) const
    { return iterTraits(DiffIter(*this, other)); }

    MultiSet(Stack<T> elems) 
      : _elems(elems.size()) 
    {
      std::sort(elems.begin(), elems.end());
      auto iter = elems.begin();
      while (iter != elems.end()) {
        auto elem = *iter++;
        auto n = IntegerConstantType(1);
        while (iter != elems.end() && *iter == elem) {
          ++n;
          iter++;
        }
        _elems.push(std::make_tuple(elem, n));
      }
    }


    void reset() { _elems.reset(); }
    bool keepRecycled() const { return _elems.keepRecycled(); }
    
    void init(T t1, T t2)
    { 
      ASS(_elems.isEmpty())
       if (t1 == t2) {
         _elems.push(std::make_pair(std::move(t1), IntegerConstantType(2)));
       } else if (t1 < t2) {
         _elems.reserve(2);
         _elems.push(std::make_pair(std::move(t1), IntegerConstantType(1)));
         _elems.push(std::make_pair(std::move(t2), IntegerConstantType(1)));
       } else {
         _elems.reserve(2);
         _elems.push(std::make_pair(std::move(t1), IntegerConstantType(1)));
         _elems.push(std::make_pair(std::move(t2), IntegerConstantType(1)));
       }
    }

 
    void init(T t)
    { 
      ASS(_elems.isEmpty())
      _elems.push(std::make_pair(std::move(t), IntegerConstantType(1)));
    }


    // MultiSet(std::initializer_list<T> elems0) : MultiSet(Stack<T>(elems0)) {}

    static MultiSet fromSortedStack(Stack<std::tuple<T, IntegerConstantType>> elems)
    {
      MultiSet out;
      out._elems = std::move(elems);
      out.integrity();
      return out;
    }

    T const& elemAt(unsigned i) const 
    { return std::get<0>(_elems[i]); }

    IntegerConstantType cntAt(unsigned i) const 
    { return std::get<1>(_elems[i]); }

    unsigned distinctElems() const 
    { return _elems.size(); }

    friend std::ostream& operator<<(std::ostream& out, MultiSet const& self)
    { 
      out << "{";
      for (auto& e : self._elems) {
        out << std::get<1>(e) << " x " << std::get<0>(e) << ", ";
      }
      out << "}";
      return out; 
    }
    friend bool operator==(MultiSet const& lhs, MultiSet const& rhs)
    { 
      lhs.integrity();
      rhs.integrity();
      return lhs._elems == rhs._elems;
    }

    friend bool operator!=(MultiSet const& lhs, MultiSet const& rhs)
    { return !(lhs == rhs); }

    void repeat(IntegerConstantType n)
    {
      ASS_G(n, IntegerConstantType(0))
      for (auto& x : _elems) {
        std::get<1>(x) *= IntegerConstantType(n);
      }
    }

    class DiffIter {
      MultiSet const& _l;
      MultiSet const& _r;
      unsigned _li;
      unsigned _ri;

    public: 

      DECL_ELEMENT_TYPE(std::tuple<T const*, unsigned>);
      DiffIter(MultiSet const& l, MultiSet  const& r) : _l(l), _r(r), _li(0), _ri(0) 
      { skipToNext(); }

      void skipToNext()
      {
        // TODO test
        while (_li < _l.distinctElems()) {
          while (_ri < _r.distinctElems() 
              && _l.elemAt(_li) > _r.elemAt(_ri)) { 
            _ri++;
          }
          if (_ri >= _r.distinctElems() || _l.elemAt(_li) < _r.elemAt(_ri)) {
            return;
          } else {
            ASS(_l.elemAt(_li) == _r.elemAt(_ri))
            auto diff = _l.cntAt(_li) - (int) _r.cntAt(_ri);
            if (diff > 0) {
              return;
            } else {
              _li++;
            }
          }
        }
      }

      bool hasNext() const { return _li < _l.distinctElems(); }
      OWN_ELEMENT_TYPE next() { 
        auto cnt_r = _ri >= _r.distinctElems() ? 0
                   : _r.elemAt(_ri) == _l.elemAt(_li) ? _r.cntAt(_ri) 
                   : 0;

        auto out = OWN_ELEMENT_TYPE(&_l.elemAt(_li), _l.cntAt(_li) - cnt_r);
        _li++;
        skipToNext();
        return out;
      }
    };

  };

  //  TODO document
  template<class A>
  struct WeightedMultiSet {
    IntegerConstantType weight;
    MultiSet<A> elems;
    WeightedMultiSet() : weight(1), elems() { }
    WeightedMultiSet(IntegerConstantType weight, MultiSet<A> elems) : weight(weight), elems(std::move(elems)) {
      ASS_G(weight, IntegerConstantType(0))
    }

    void reset() { elems.reset(); weight = IntegerConstantType(1); }
    bool keepRecycled() const { return elems.keepRecycled(); }

    friend std::ostream& operator<<(std::ostream& out, WeightedMultiSet const& self)
    { return out << "(1 / " << self.weight << ") " << self.elems; }

    friend bool operator==(WeightedMultiSet const& lhs, WeightedMultiSet const& rhs)
    { return lhs.weight == rhs.weight && lhs.elems == rhs.elems; }

    friend bool operator!=(WeightedMultiSet const& lhs, WeightedMultiSet const& rhs)
    { return !(lhs == rhs); }

  };


  class OrderingUtils {
  public:
    using MulExtMemo = DArray<Option<Ordering::Result>>;

    enum class SelectionCriterion {
      NOT_LEQ,
      NOT_LESS,
      STRICTLY_MAX,
      ANY,
    };

    static bool notLeq(Ordering::Result r) 
    { return r != Ordering::Result::LESS 
          && r != Ordering::Result::EQUAL; }

    static bool notLess(Ordering::Result r) 
    { return r != Ordering::Result::LESS; }

    template<class T>
    static Ordering::Result stdCompare(T const& l, T const& r) 
    { 
      return l < r ? Ordering::Result::LESS 
           : l > r ? Ordering::Result::GREATER 
           : l == r ? Ordering::Result::EQUAL
           : Ordering::Result::INCOMPARABLE; 
    }

    template<class Cmp, class GetElem>
    static auto maxElems(unsigned nElems, Cmp cmp_, GetElem get, SelectionCriterion sel, bool dedup = false)
    {
      auto cmpCache = Lib::make_shared(Map<std::pair<unsigned, unsigned>, Ordering::Result>());

      auto cmp = [=](unsigned l, unsigned r) {
        ASS_NEQ(l, r)
        unsigned col = l < r ? l : r;
        unsigned row = l < r ? r : l;


        auto idx = std::make_pair(col, row);
        auto res = cmpCache->getOrInit(idx, [&]() { return cmp_(col, row); });

        res = l < r ? res : Ordering::reverse(res);

        ASS_REP(res == cmp_(l, r), Output::cat(get(l), " ", cmp_(l, r), " ", get(r), " expected: ", res ))
        return res;
      };


      return range(0, nElems)
        .filterMap([=](auto i) -> Option<unsigned> {
          if (sel == SelectionCriterion::ANY) 
            return some(i);

          if (dedup && range(0, i).any([&](auto j) { return cmp(i,j) == Ordering::Result::EQUAL; }))
            return {};

          auto matches = [](SelectionCriterion sel, Ordering::Result res)  {
            switch(sel) {
              case SelectionCriterion::ANY: return true;
              case SelectionCriterion::NOT_LESS:
                switch(res) {
                  case Ordering::Result::INCOMPARABLE:
                  case Ordering::Result::GREATER:
                  case Ordering::Result::EQUAL: 
                    return true;
                  case Ordering::Result::LESS:
                    return false;
                }
              case SelectionCriterion::NOT_LEQ:
                switch(res) {
                  case Ordering::Result::INCOMPARABLE:
                  case Ordering::Result::GREATER:
                    return true;
                  case Ordering::Result::LESS:
                  case Ordering::Result::EQUAL: 
                    return false;
                }
              case SelectionCriterion::STRICTLY_MAX:
                switch(res) {
                  case Ordering::Result::GREATER:
                    return true;
                  case Ordering::Result::INCOMPARABLE:
                  case Ordering::Result::LESS:
                  case Ordering::Result::EQUAL: 
                    return false;
                }
            }
            ASSERTION_VIOLATION
          };

          bool isMax = range(0, nElems)
            .filter([&](auto j) { return i != j; })
            .all([&](auto j) { return matches(sel, cmp(i,j)); });

          return isMax ? Option<unsigned>(i) : Option<unsigned>();
        })
      ;
    }


    template<class Ord>
    static Ordering::Result lexProductCapture(Ord ord)
    { return ord(); }

    template<class Ord1, class Ord2, class... Ords>
    static Ordering::Result lexProductCapture(Ord1 ord1, Ord2 ord2, Ords... ords)
    { 
      auto c = ord1();
      switch(c) {
        case Ordering::Result::EQUAL: 
          return OrderingUtils::lexProductCapture(ord2,ords...);
        case Ordering::Result::INCOMPARABLE: 
        case Ordering::Result::GREATER: 
        case Ordering::Result::LESS: 
          return c;
        default:;
      }
      ASSERTION_VIOLATION_REP(c)
    }

    template<class Ord>
    static auto lexProduct(Ord ord) 
    { return ord; }

    template<class Ord1, class Ord2, class... Ords>
    static auto lexProduct(Ord1 ord1, Ord2 ord2, Ords... ords) 
    { 
      return [=](auto const& l, auto const& r) { 
        auto c = ord1(l,r);
        switch(c) {
          case Ordering::Result::EQUAL: 
            return OrderingUtils::lexProduct(ord2,ords...)(l,r);
          case Ordering::Result::INCOMPARABLE: 
          case Ordering::Result::GREATER: 
          case Ordering::Result::LESS: 
            return c;
          default:;
        }
        ASSERTION_VIOLATION_REP(c)
      };
    }

  private:
    template<class A, class B, class Cmp> 
    static Ordering::Result _mulExt(
        MultiSet<A> const& ls, IntegerConstantType mulL, 
        MultiSet<B> const& rs, IntegerConstantType mulR, 
        Cmp cmp_, Option<MulExtMemo&> memo)
    {
      memo.andThen([&](auto& memo) {
          if (memo.size() == 0) 
            memo = MulExtMemo::initialized(ls.distinctElems() * rs.distinctElems());
      });
      auto cmp = [&memo, &ls, &rs, &cmp_](unsigned i, unsigned j) {
        return memo.match(
            [&](auto& memo) { 
              auto idx = i + j * ls.distinctElems();
              if (memo[idx].isNone()) {
                memo[idx] = Option<Ordering::Result>(cmp_(ls.elemAt(i), rs.elemAt(j)));
              } 
              return memo[idx].unwrap();
            },
            [&]() { return cmp_(ls.elemAt(i), rs.elemAt(j)); });
      };

      auto l = iterTraits(getRangeIterator<unsigned>(0, ls.distinctElems()))
            .map([&](auto i){ return std::make_tuple(i, ls.cntAt(i) * mulL); } )
            .template collect<Stack>();
      auto r = iterTraits(getRangeIterator<unsigned>(0, rs.distinctElems()))
            .map([&](auto i){ return std::make_tuple(i, rs.cntAt(i) * mulR); } )
            .template collect<Stack>();

      auto getCount = [](std::tuple<unsigned, IntegerConstantType>& tup) -> IntegerConstantType&
        { return std::get<1>(tup); };

      auto getElem = [](std::tuple<unsigned, IntegerConstantType>& tup) -> unsigned
        { return std::get<0>(tup); };

      // removing duplicates
      for (unsigned il = 0; il < l.size();) {
        auto& i = l[il];
        for(unsigned ir = 0; ir < r.size();) {
          auto& j = r[ir];
          if (cmp(getElem(i), getElem(j)) == Ordering::Result::EQUAL) {
            auto min = std::min(getCount(i), getCount(j));
            getCount(i) -= min;
            getCount(j) -= min;
            ASS(getCount(i) == IntegerConstantType(0) || getCount(j) == IntegerConstantType(0));
            if (getCount(i) == IntegerConstantType(0))
              l.swapRemove(il);
            if (getCount(j) == IntegerConstantType(0))
              r.swapRemove(ir);
            goto continue_outer;
          } else {
            ir++;
          }
        }
        il++;
    continue_outer:;
      }


      if (l.size() == 0 && r.size() == 0 ) return Ordering::EQUAL;
      else if (l.size() == 0)              return Ordering::LESS;
      else if (r.size() == 0)              return Ordering::GREATER;
      else {

        if (iterTraits(l.iter())
              .all([&](auto i) { return iterTraits(r.iter())
                .any([&](auto j) 
                  { return cmp(getElem(i),getElem(j)) == Ordering::LESS; }); })) {
          return Ordering::LESS;
        } else if (iterTraits(r.iter())
              .all([&](auto j) { return iterTraits(l.iter())
                .any([&](auto i) 
                  { return cmp(getElem(i),getElem(j)) == Ordering::GREATER; }); })) {
          return Ordering::GREATER;
        } else {
          // all are incomparable
          return Ordering::INCOMPARABLE;
        }

      }
    }


  public:
    template<class Iter1, class Iter2, class Cmp>
    static auto lexExt(Iter1 ls, Iter2 rs, Cmp cmp) {
      while (ls.hasNext()) {
        ASS(rs.hasNext())
        auto l = ls.next();
        auto r = rs.next();
        auto c = cmp(l,r);
        if (c != Ordering::Result::EQUAL) 
          return c;
      }
      ASS(!rs.hasNext());
      return Ordering::Result::EQUAL;
    }


    template<class A, class B, class Cmp> 
    static Ordering::Result weightedMulExt(WeightedMultiSet<A> const& l, WeightedMultiSet<B> const& r, Cmp cmp)
    { MulExtMemo memo; return weightedMulExt(l, r, cmp, memo); }


    template<class A, class B, class Cmp> 
    static Ordering::Result weightedMulExtWithoutMemo(WeightedMultiSet<A> const& l, WeightedMultiSet<B> const& r, Cmp cmp)
    { return _mulExt(l.elems, r.weight, r.elems, l.weight, cmp, Option<MulExtMemo&>()); }

    template<class A, class B, class Cmp> 
    static Ordering::Result weightedMulExt(WeightedMultiSet<A> const& l, WeightedMultiSet<B> const& r, Cmp cmp, MulExtMemo& memo)
    { return _mulExt(l.elems, r.weight, r.elems, l.weight, cmp, Option<MulExtMemo&>(memo)); }



    template<class A, class B, class Cmp> 
    static Ordering::Result mulExt(MultiSet<A> const& l, MultiSet<B> const& r, Cmp cmp)
    { MulExtMemo memo; return mulExt(l, r, cmp, memo); }

    template<class A, class B, class Cmp> 
    static Ordering::Result mulExtWithoutMemo(MultiSet<A> const& l, MultiSet<B> const& r, Cmp cmp)
    { return _mulExt(l, IntegerConstantType(1), r, IntegerConstantType(1), cmp, Option<MulExtMemo&>()); }

    template<class A, class B, class Cmp> 
    static Ordering::Result mulExt(MultiSet<A> const& l, MultiSet<B> const& r, Cmp cmp, MulExtMemo& memo)
    { return _mulExt(l, IntegerConstantType(1), r, IntegerConstantType(1), cmp, Option<MulExtMemo&>(memo)); }

  };


}

#endif // __OrderingUtils__
