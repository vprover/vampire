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
 * @file UnitHashingIndex.hpp
 * Defines class UnitHashingIndex.
 */

#ifndef __UnitHashingIndex__
#define __UnitHashingIndex__

#include "Forwards.hpp"
#include "Index.hpp"

namespace Indexing {

class UnitHashingIndex : public Index {
public:
  Clause* getUnitLikeThis(Clause* c, bool opposite);
protected:
  virtual void handleClause(Clause* c, bool adding);
private:
  DHMap<Literal*,Clause*> _lookup;
};

}

#endif // __UnitHashingIndex__
