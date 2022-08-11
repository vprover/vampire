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

#include "Kernel/MismatchHandler.hpp"

namespace Indexing {

template<class T>
class LascaIndex : public Indexing::Index
{
public:
  CLASS_NAME(LascaIndex);
  USE_ALLOCATOR(LascaIndex);

  LascaIndex(Kernel::MismatchHandler* hndlr = 0)
    : _index(hndlr)
    , _shared()
  {}

  void setShared(shared_ptr<Kernel::LascaState> shared) { _shared = std::move(shared); }

  // TODO remove?!
  auto find(TermList key, TermList sort)
  { 
    CALL("LascaIndex::find")
    return iterTraits(_index.getUnificationsUsingSorts(key,sort, /* retrieveSubstitutions */ true))
      .map([](TermQueryResult<T> r) 
           { return std::tuple<T, UwaResult>( std::move(r.data()), UwaResult(r));  })
      .timeTraced(_lookupStr.c_str()); }


  auto generalizations(TermList key, bool retrieveSubstitutions = true)
  { return iterTraits(_index.getGeneralizations(key, retrieveSubstitutions)); }

  auto instances(TermList key, bool retrieveSubstitutions = true)
  { return iterTraits(_index.getInstances(key, retrieveSubstitutions)); }

  virtual void handleClause(Clause* c, bool adding) final override 
  {
    CALL("LascaIndex::handleClause")
    TIME_TRACE(_maintainanceStr.c_str())
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
  static vstring _lookupStr;
  static vstring _maintainanceStr;
};

template<class T> vstring LascaIndex<T>::_lookupStr = T::name() + vstring(" lookup");
template<class T> vstring LascaIndex<T>::_maintainanceStr = T::name() + vstring(" maintainance");

} // namespace Indexing

#endif // __LASCA_LascaIndex__
