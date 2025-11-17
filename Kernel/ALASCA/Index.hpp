/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __ALASCA_AlascaIndex__
#define __ALASCA_AlascaIndex__


#include "Indexing/SubstitutionTree.hpp"
#include "Kernel/ALASCA.hpp"

#include "Debug/TimeProfiling.hpp"
#include "Indexing/Index.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Kernel/TypedTermList.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Indexing {

template<class C>
using KeyType = decltype(assertionViolation<C>().key());

// TODO move this to some other place maybe?
template<class T, class C> struct GenSubstitutionTree_;
template<class T         > struct GenSubstitutionTree_<T, Literal*     > { using Type = LiteralSubstitutionTree<T>; };
template<class T         > struct GenSubstitutionTree_<T, TypedTermList> { using Type = TermSubstitutionTree<T>;    };

template<class T>
using GenSubstitutionTree = typename GenSubstitutionTree_<T, KeyType<T>>::Type;

template<class T>
class AlascaIndex : public Indexing::Index
{
public:
  USE_ALLOCATOR(AlascaIndex);

  AlascaIndex()
    : _index()
    , _shared()
  {}

  void setShared(std::shared_ptr<Kernel::AlascaState> shared) { _shared = std::move(shared); }

  template<class VarBanks>
  auto find(AbstractingUnifier* state, KeyType<T> key)
  { return iterTraits(_index.template getUwa<VarBanks>(state, key, _shared->uwaMode(), _shared->uwaFixedPointIteration))
      .timeTraced(_lookupStr.c_str()); }


  auto generalizations(TypedTermList key, bool retrieveSubstitutions = true)
  { return iterTraits(_index.getGeneralizations(key, retrieveSubstitutions)); }

  auto instances(TypedTermList key, bool retrieveSubstitutions = true)
  { return iterTraits(_index.getInstances(key, retrieveSubstitutions)); }

  void handleClause(Clause* c, bool adding) final
  {
    TIME_TRACE(_maintenanceStr.c_str())
    for (auto appl : T::iter(*_shared, c)) {
      if (adding) {
#if VDEBUG
        auto k = appl.key();
#endif
        _index.insert(std::move(appl));
        DEBUG_CODE(
        auto state = AbstractingUnifier::empty(AbstractionOracle(Shell::Options::UnificationWithAbstraction::OFF));
        )
        ASS_REP(find<RetrievalAlgorithms::DefaultVarBanks>(&state, k).hasNext(), Output::cat("key: ", Output::ptr(k), "\nindex: ", Output::multiline(_index)))
      } else {
        _index.remove(std::move(appl));
      }
    }
  }

private:
  GenSubstitutionTree<T> _index;
  std::shared_ptr<Kernel::AlascaState> _shared;
  static std::string _lookupStr;
  static std::string _maintenanceStr;
};

template<class T> std::string AlascaIndex<T>::_lookupStr = T::name() + std::string(" lookup");
template<class T> std::string AlascaIndex<T>::_maintenanceStr = T::name() + std::string(" maintenance");

} // namespace Indexing

#undef DEBUG

#endif // __ALASCA_AlascaIndex__
