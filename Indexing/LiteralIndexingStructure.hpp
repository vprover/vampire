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
#include "Shell/Options.hpp"

namespace Indexing {

class LiteralIndexingStructure {
public:
  virtual ~LiteralIndexingStructure() {}

  virtual void insert(Literal* lit, Clause* cls) = 0;
  virtual void remove(Literal* lit, Clause* cls) = 0;

  virtual VirtualIterator<LQueryRes<SmartPtr<ResultSubstitution>>> getAll() { NOT_IMPLEMENTED; }
  virtual VirtualIterator<LQueryRes<SmartPtr<ResultSubstitution>>> getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual VirtualIterator<LQueryRes<AbstractingUnifier*>> getUwa(Literal* lit, bool complementary, Options::UnificationWithAbstraction uwa, bool fixedPointIteration) = 0;
  virtual VirtualIterator<LQueryRes<SmartPtr<GenSubstitution>>> getGeneralizations(Literal* lit, bool complementary, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual VirtualIterator<LQueryRes<SmartPtr<InstSubstitution>>> getInstances(Literal* lit, bool complementary, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual VirtualIterator<LQueryRes<SmartPtr<ResultSubstitution>>> getVariants(Literal* lit, bool complementary, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }

  virtual size_t getUnificationCount(Literal* lit, bool complementary)
  {
    CALL("LiteralIndexingStructure::getUnificationCount");
    return countIteratorElements(getUnifications(lit, complementary, false));
  }

#if VDEBUG
  virtual void markTagged() = 0;
#endif

};

};

#endif /* __LiteralIndexingStructure__ */
