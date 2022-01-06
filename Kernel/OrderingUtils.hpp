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

#include "Lib/Option.hpp"
#include "Kernel/Ordering.hpp"

namespace Kernel {
  using namespace Lib;

  class OrderingUtils {
  public:
    using MulExtMemo = DArray<Option<Ordering::Result>>;
  private:

    template<class Cmp> 
    static Ordering::Result _mulExt(unsigned lsz, unsigned rsz, Cmp cmp_, Option<MulExtMemo&> memo)
    {
      CALL("mulExt")
      memo.andThen([&](auto& memo){
          if (memo.size() == 0) 
            memo = MulExtMemo::initialized(lsz * rsz);
      });
      auto cmp = [&](unsigned i, unsigned j) {
        return memo.match(
            [&](auto& memo) { 
              auto idx = i + j * lsz;
              if (memo[idx].isNone()) {
                memo[idx] = Option<Ordering::Result>(cmp_(i, j));
              } 
              return memo[idx].unwrap();
            },
            [&]() { return cmp_(i,j); });
      };

      auto l = Stack<unsigned>::fromIterator(getRangeIterator<unsigned>(0, lsz));
      auto r = Stack<unsigned>::fromIterator(getRangeIterator<unsigned>(0, rsz));

      // removing duplicates
      for (unsigned il = 0; il < l.size();) {
        auto i = l[il];
        for(unsigned ir = 0; ir < r.size();) {
          auto j = r[ir];
          if (cmp(i, j) == Ordering::Result::EQUAL) {
            l.swapRemove(il);
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
                  { return cmp(i,j) == Ordering::LESS; }); })) {
          return Ordering::LESS;
        } else if (iterTraits(r.iter())
              .all([&](auto j) { return iterTraits(l.iter())
                .any([&](auto i) 
                  { return cmp(i,j) == Ordering::GREATER; }); })) {
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



    template<class Cmp> 
    static Ordering::Result mulExt(unsigned lsz, unsigned rsz, Cmp cmp)
    { MulExtMemo memo; return mulExt(lsz, rsz, cmp, memo); }


    template<class Cmp> 
    static Ordering::Result mulExtWithoutMemo(unsigned lsz, unsigned rsz, Cmp cmp)
    { return _mulExt(lsz, rsz, cmp, Option<MulExtMemo&>()); }

    template<class Cmp> 
    static Ordering::Result mulExt(unsigned lsz, unsigned rsz, Cmp cmp, MulExtMemo& memo)
    { return _mulExt(lsz, rsz, cmp, Option<MulExtMemo&>(memo)); }

    template<class A, class Cmp> 
    static Ordering::Result mulExt(Stack<A> const& l, Stack<A> const& r, Cmp cmp)
    { return mulExt(l.size(), r.size(), [&](unsigned i, unsigned j) { return cmp(l[i], r[j]); }); }

    template<class A, class Cmp> 
    static Option<A> strictlyMax(Stack<A> elems, Cmp cmp) 
    {
      for (unsigned i = 0; i < elems.size(); i++) {
        for (unsigned j = 0; j < elems.size(); j++) {
          if (i != j) {
            auto c = cmp(elems[i], elems[j]);
            if (c != Ordering::GREATER)  {
              goto not_greater;
            }
          }
        }
        return Option<A>(elems[i]);
not_greater:;
      }
      return Option<A>();
    }
  };

}

#endif // __OrderingUtils__
