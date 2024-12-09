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
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Kernel/TypedTermList.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Indexing {

template<class C>
using KeyType = decltype(assertionViolation<C>().key());

template<class T, class C> struct GenSubstitutionTree_;
template<class T         > struct GenSubstitutionTree_<T, Literal*     > { using Type = LiteralSubstitutionTree<T>; };
template<class T         > struct GenSubstitutionTree_<T, TypedTermList> { using Type = TermSubstitutionTree<T>;    };

template<class T>
using GenSubstitutionTree = typename GenSubstitutionTree_<T, KeyType<T>>::Type;

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

  // auto find(TypedTermList key, unsigned queryBankNumber, AbstractingUnifier* state)
  // { return iterTraits(_index.getUwa(key, queryBankNumber, _shared->uwaMode(), _shared->uwaFixedPointIteration, state))
  //     .timeTraced(_lookupStr.c_str()); }

  auto find(AbstractingUnifier* state, KeyType<T> key, int queryBank, int normInternalBank, int internalBank)
  { return iterTraits(_index.getUwa(state, key
        , queryBank, normInternalBank, internalBank
        , _shared->uwaMode(), _shared->uwaFixedPointIteration))
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
        DEBUG_CODE(
        auto state = AbstractingUnifier::empty(AbstractionOracle(Shell::Options::UnificationWithAbstraction::OFF));
        )
        ASS_REP(find(&state, k, 0, 1, 2).hasNext(), outputToString("key: ", outputMaybePtr(k), "\nindex: ", multiline(_index)))
      } else {
        _index.remove(std::move(appl));
      }
    }
  }

private:
  GenSubstitutionTree<T> _index;
  std::shared_ptr<Kernel::LascaState> _shared;
  static std::string _lookupStr;
  static std::string _maintainanceStr;
};

template<class T> std::string LascaIndex<T>::_lookupStr = T::name() + std::string(" lookup");
template<class T> std::string LascaIndex<T>::_maintainanceStr = T::name() + std::string(" maintainance");

} // namespace Indexing

#undef DEBUG

#endif // __LASCA_LascaIndex__
