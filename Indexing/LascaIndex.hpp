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
#include "Debug/TimeProfiling.hpp"
#include "Indexing/Index.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Kernel/TypedTermList.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Indexing {

template<class T>
class LascaIndex : public Indexing::Index
{
public:
  USE_ALLOCATOR(LascaIndex);

  LascaIndex()
    : _index()
    , _shared()
  {}

  void setShared(std::shared_ptr<Kernel::LascaState> shared) { _shared = std::move(shared); }

  auto find(TypedTermList key)
  {
    return iterTraits(_index.getUwa(key, _shared->uwaMode(), _shared->uwaFixedPointIteration))
      .timeTraced(_lookupStr.c_str()); }


  auto generalizations(TypedTermList key, bool retrieveSubstitutions = true)
  { return iterTraits(_index.getGeneralizations(key, retrieveSubstitutions)); }

  auto instances(TypedTermList key, bool retrieveSubstitutions = true)
  { return iterTraits(_index.getInstances(key, retrieveSubstitutions)); }

  virtual void handleClause(Clause* c, bool adding) final override
  {
    TIME_TRACE(_maintainanceStr.c_str())
    for (auto appl : T::iter(*_shared, c)) {
      if (adding) {
#if VDEBUG
        auto k = appl.key();
#endif
        _index.insert(std::move(appl));
        ASS_REP(find(k).hasNext(), outputToString("key: ", k, "\nindex: ", multiline(_index)))
      } else {
        _index.remove(std::move(appl));
      }
    }
  }

private:
  TermSubstitutionTree<T> _index;
  std::shared_ptr<Kernel::LascaState> _shared;
  static vstring _lookupStr;
  static vstring _maintainanceStr;
};

template<class T> vstring LascaIndex<T>::_lookupStr = T::name() + vstring(" lookup");
template<class T> vstring LascaIndex<T>::_maintainanceStr = T::name() + vstring(" maintainance");

} // namespace Indexing

#undef DEBUG

#endif // __LASCA_LascaIndex__
