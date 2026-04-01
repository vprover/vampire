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
#include "Kernel/UnificationWithAbstraction.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Shell/Options.hpp"
#include "IndexingStructure.hpp"

namespace Indexing {

template<class Data>
class LiteralIndexingStructure : public IndexingStructure<Data> {
public:
  virtual VirtualIterator<QueryRes<ResultSubstitutionSP, Data>> getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual VirtualIterator<QueryRes<AbstractingUnifier*, Data>> getUwa(Literal* lit, bool complementary, Options::UnificationWithAbstraction uwa, bool fixedPointIteration) = 0;
  virtual VirtualIterator<QueryRes<ResultSubstitutionSP, Data>> getGeneralizations(Literal* lit, bool complementary, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual VirtualIterator<QueryRes<ResultSubstitutionSP, Data>> getInstances(Literal* lit, bool complementary, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
  virtual VirtualIterator<QueryRes<ResultSubstitutionSP, Data>> getVariants(Literal* lit, bool complementary, bool retrieveSubstitutions = true) { NOT_IMPLEMENTED; }
};

};

#endif /* __LiteralIndexingStructure__ */
