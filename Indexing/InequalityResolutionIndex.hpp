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
 * @file InequalityResolutionIndex.hpp
 * Defines class InequalityResolutionIndex
 *
 */

#ifndef __IRC_InequalityResolutionIndex__
#define __IRC_InequalityResolutionIndex__


#include "Kernel/IRC.hpp"

#include "Indexing/IndexManager.hpp"
#include "Indexing/TermIndex.hpp"
#include "Indexing/Index.hpp"
#include "Indexing/TermSubstitutionTree.hpp"

namespace Indexing {

template<class T>
class IrcIndex : public Indexing::Index
{
public:
  CLASS_NAME(IrcIndex);
  USE_ALLOCATOR(IrcIndex);

  IrcIndex(Options::UnificationWithAbstraction uwa)
    : _index(uwa, /* use constraints */  true)
    , _shared()
  {  }

  void setShared(shared_ptr<Kernel::IrcState> shared) { _shared = std::move(shared); }

  // void setShared(shared_ptr<Kernel::IrcState> shared) { _shared = std::move(shared); }
  // TODO remove?!
  auto find(TermList key)
  { return iterTraits(_index.getUnificationsWithConstraints(key, /* retrieveSubstitutions */ true))
      .map([](TermQueryResult<T> r) 
           { return std::tuple<T, UwaResult>( std::move(r.data()), UwaResult(r));  }); }


  virtual void handleClause(Clause* c, bool adding) final override 
  {
    for (auto appl : T::iter(*_shared, c)) {
      if (adding) {
        // TODO this is very hacky. implement nicer ?!
        _index.insert(std::move(appl));
      } else {
        _index.remove(std::move(appl));
      }
    }
  }

private:
  TermSubstitutionTree<T> _index;
  shared_ptr<Kernel::IrcState> _shared;
};

} // namespace Indexing

#endif // __IRC_InequalityResolutionIndex__
