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
 * @file LascaIndex.hpp
 * Defines class LascaIndex
 *
 */

#ifndef __LASCA_LascaIndex__
#define __LASCA_LascaIndex__


#include "Kernel/LASCA.hpp"

#include "Indexing/IndexManager.hpp"
#include "Indexing/TermIndex.hpp"
#include "Indexing/Index.hpp"
#include "Indexing/TermSubstitutionTree.hpp"

namespace Indexing {

template<class T>
class LascaIndex : public Indexing::Index
{
public:
  CLASS_NAME(LascaIndex);
  USE_ALLOCATOR(LascaIndex);

  LascaIndex(Options::UnificationWithAbstraction uwa)
    : _index(uwa, /* use constraints */  true)
    , _shared()
  {  }

  void setShared(shared_ptr<Kernel::LascaState> shared) { _shared = std::move(shared); }

  // void setShared(shared_ptr<Kernel::LascaState> shared) { _shared = std::move(shared); }
  // TODO remove?!
  auto find(TermList key)
  { 
    CALL("LascaIndex::find")
    return iterTraits(_index.getUnificationsWithConstraints(key, /* retrieveSubstitutions */ true))
      .map([](TermQueryResult<T> r) 
           { return std::tuple<T, UwaResult>( std::move(r.data()), UwaResult(r));  })
      .timeTraced("lasca index lookup"); }


  virtual void handleClause(Clause* c, bool adding) final override 
  {
    CALL("LascaIndex::handleClause")
    TIME_TRACE("lasca index maintance")
    for (auto appl : T::iter(*_shared, c)) {
      if (adding) {
        _index.insert(std::move(appl));
      } else {
        _index.remove(std::move(appl));
      }
    }
  }

private:
  TermSubstitutionTree<T> _index;
  shared_ptr<Kernel::LascaState> _shared;
};

} // namespace Indexing

#endif // __LASCA_LascaIndex__
