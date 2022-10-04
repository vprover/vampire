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

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Indexing {

template<class T>
class LascaIndex : public Indexing::Index
{
public:
  CLASS_NAME(LascaIndex);
  USE_ALLOCATOR(LascaIndex);

  LascaIndex(Options::UnificationWithAbstraction uwa)
    : _index(uwa, /* use constraints */  true)
    , _uwa(uwa)
    , _shared()
  {}

  void setShared(shared_ptr<Kernel::LascaState> shared) { _shared = std::move(shared); }

  auto find(TermList key)
  {
    CALL("LascaIndex::find")
    return iterTraits(_index.getUnificationsWithConstraints(key, /* retrieveSubstitutions */ true))
      .map([](TermQueryResult<T> r)
           { return std::tuple<T, UwaResult>( std::move(r.data()), UwaResult(r));  })
      .filter([=](auto& x) {
          Stack<UnificationConstraint> c;
          UWAMismatchHandler hndlr(_uwa, c);
          auto result = get<1>(x).cnstLiterals()
            .all([&](auto lit) {
                ASS(lit->isEquality() && lit->isNegative())
                return hndlr.checkUWA(lit->termArg(0), lit->termArg(1));
            });
          if (!result) { DEBUG("skipping wrong constraints: ", c) }
          ASS(c.isEmpty());
          return result;
      })
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
        ASS(find(appl.key()).hasNext())
      } else {
        _index.remove(std::move(appl));
      }
    }
  }

private:
  TermSubstitutionTree<T> _index;
  Options::UnificationWithAbstraction _uwa;
  shared_ptr<Kernel::LascaState> _shared;
  static vstring _lookupStr;
  static vstring _maintainanceStr;
};

template<class T> vstring LascaIndex<T>::_lookupStr = T::name() + vstring(" lookup");
template<class T> vstring LascaIndex<T>::_maintainanceStr = T::name() + vstring(" maintainance");

} // namespace Indexing

#undef DEBUG

#endif // __LASCA_LascaIndex__
