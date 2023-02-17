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
 * @file LiteralIndexingStructure.hpp
 * Defines class LiteralIndexingStructure.
 */


#ifndef __LiteralIndexingStructure__
#define __LiteralIndexingStructure__

#include "Forwards.hpp"
#include "Index.hpp"
#include "Kernel/MismatchHandler.hpp"
#include "Lib/VirtualIterator.hpp"

namespace Indexing {

template<class LeafData_ = DefaultLiteralLeafData>
class LiteralIndexingStructure {
public:
  using LeafData = LeafData_;
  virtual ~LiteralIndexingStructure() {}

  virtual void handle(LeafData ld, bool insert) = 0;
  void insert(LeafData ld) { handle(std::move(ld), /* insert = */ true ); }
  void remove(LeafData ld) { handle(std::move(ld), /* insert = */ false); }

  virtual VirtualIterator<LeafData> getAll() { NOT_IMPLEMENTED; }
  virtual VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData>> getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual VirtualIterator<QueryRes<AbstractingUnifier*, LeafData>> getUwa(Literal* lit, bool complementary) = 0;
  virtual VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData>> getGeneralizations(Literal* lit, bool complementary, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData>> getInstances(Literal* lit, bool complementary, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual VirtualIterator<QueryRes<ResultSubstitutionSP, LeafData>> getVariants(Literal* lit, bool complementary, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }

  virtual size_t getUnificationCount(Literal* lit, bool complementary)
  {
    CALL("LiteralIndexingStructure::getUnificationCount");
    return countIteratorElements(getUnifications(lit, complementary, false));
  }

};

};

#endif /* __LiteralIndexingStructure__ */
