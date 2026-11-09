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
 * @file TermCodeTree.hpp
 * Defines class TermCodeTree.
 */

#ifndef __TermCodeTree__
#define __TermCodeTree__

#include "Forwards.hpp"

#include "Kernel/Matcher.hpp"
#include "Kernel/TypedTermList.hpp"

#include "TermOrLiteralCodeTree.hpp"

namespace Indexing {

using namespace Lib;
using namespace Kernel;

template<class Data>
class TermCodeTree : public TermOrLiteralCodeTree<Data>
{
public:
  struct TermMatcher
  : public TermOrLiteralCodeTree<Data>::Matcher
  {
    using Base = TermOrLiteralCodeTree<Data>::Matcher;
    using Base::ft;
    using Base::op;

    void init(const CodeTree& tree, TypedTermList t) {
      Base::init(tree, FlatTerm::create(t));
      _querySort = t.sort();
    }

    Data* next() {
      if (Base::finished()) {
        //all possible matches are exhausted
        return 0;
      }

      while ((Base::_matched=Base::execute())) {
        ASS(op->isSuccess());
        auto res = op->template getSuccessResult<Data>();
        if (res->key().isVar()) {
          // match the variable sort separately
          Substitution subst;
          if (!MatchingUtils::matchTerms(res->key().sort(), _querySort, subst)) {
            continue;
          }
          for (const auto& [v,t] : iterTraits(subst.items())) {
            ASS_G(v, 0); // X0 is reserved for the term itself
            Base::bindings[v] = t;
          }
        }
        return res;
      }
      return nullptr;
    }

  private:
    TermList _querySort;
  };
};

};

#endif // __TermCodeTree__
