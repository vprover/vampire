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


#include "Debug/Tracer.hpp"
#include "Indexing/SubstitutionTree.hpp"
#include "Kernel/ALASCA.hpp"

#include "Indexing/IndexManager.hpp"
#include "Indexing/TermIndex.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Indexing/Index.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Kernel/TypedTermList.hpp"
#include <type_traits>

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


  template<class T2>
  auto generalizations(T2 const& key, bool retrieveSubstitutions = true)
  { return iterTraits(_index.getGeneralizations(key.key(), retrieveSubstitutions, firstFreshVar(key))); }

  template<class T2>
  auto instances(T2 const& key, bool retrieveSubstitutions = true)
  { return iterTraits(_index.getInstances(key.key(), retrieveSubstitutions)); }

// #define INSERT_FIND_ASSERTION(...) __VA_ARGS__
#define INSERT_FIND_ASSERTION(...) {}

  virtual void handleClause(Clause* c, bool adding) final override
  {
    TIME_TRACE(_maintenanceStr.c_str())
    for (auto appl : T::iter(*_shared, c)) {
      if (adding) {
        INSERT_FIND_ASSERTION(DEBUG_CODE( 
          auto k = appl.key(); 
        ))
        _index.insert(std::move(appl));
        INSERT_FIND_ASSERTION(DEBUG_CODE(
          auto state = AbstractingUnifier::empty(AbstractionOracle(Shell::Options::UnificationWithAbstraction::OFF));
          ASS_REP(find<RetrievalAlgorithms::DefaultVarBanks>(&state, k).hasNext(), Output::cat("key: ", Output::ptr(k), "\nindex: ", Output::multiline(_index)))
        ))
      } else {
        _index.remove(std::move(appl));
      }
    }
  }

  void outputContents() { return outputContents((KeyType<T>*)nullptr); }

  void outputContents(Literal**) { }
  void outputContents(TypedTermList*) {
    DEBUG("contents of ", T::name(), ": ")
    DBG_INDENT
    auto sigma = AbstractingUnifier::empty(AbstractionOracle(Shell::Options::UnificationWithAbstraction::OFF));
    for (auto x : find<Indexing::RetrievalAlgorithms::DefaultVarBanks>(&sigma, TypedTermList(TermList::var(0), TermList::var(1)))) {
      DEBUG(x)
    }
    DEBUG("end of contents of ", T::name())
  }

  friend std::ostream& operator<<(std::ostream& out, AlascaIndex const& self)
  { return out << self._index; }
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
