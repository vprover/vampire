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

#ifndef __InequalityResolutionCalculus_InequalityResolutionIndex__
#define __InequalityResolutionCalculus_InequalityResolutionIndex__


#include "Kernel/InequalityResolutionCalculus.hpp"

#include "Indexing/IndexManager.hpp"
#include "Indexing/TermIndex.hpp"
#include "Indexing/Index.hpp"

namespace Indexing {

class InequalityResolutionIndex
: public TermIndex
{
public:
  CLASS_NAME(InequalityResolutionIndex);
  USE_ALLOCATOR(InequalityResolutionIndex);

  InequalityResolutionIndex(TermIndexingStructure* is)
    : TermIndex(is) {}

  InequalityNormalizer const& normalizer() const { return _shared->normalizer; }
  Ordering* ord() const { return _shared->ordering; }
  void setShared(shared_ptr<Kernel::IrcState> shared) { _shared = std::move(shared); }
protected:
  void handleClause(Clause* c, bool adding);
private:
  template<class NumTraits> bool handleLiteral(Literal* lit, Clause* c, bool adding);

  shared_ptr<Kernel::IrcState> _shared;
};

} // namespace Indexing

#endif // __InequalityResolutionCalculus_InequalityResolutionIndex__
