/**
 * @file AcyclicityIndex.hpp
 * Defines class AcyclicityIndex
 */

#ifndef __AcyclicityIndex__
#define __AcyclicityIndex__

#include "Indexing/Index.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Term.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/List.hpp"

#include "Forwards.hpp"

namespace Indexing {

class AcyclicityIndex
: public Index
{
public:
  AcyclicityIndex(Kernel::Ordering &ord) :
    _sIndexes(),
    _ord(ord)
  {}

  ~AcyclicityIndex() {}
  
  void insert(Kernel::Literal *lit, Kernel::Clause *c);
  void remove(Kernel::Literal *lit, Kernel::Clause *c);

  CLASS_NAME(AcyclicityIndex);
  USE_ALLOCATOR(AcyclicityIndex);
protected:
  void handleClause(Kernel::Clause* c, bool adding);
private:
  struct SubtermIterator;
  struct IndexEntry;
  
  typedef Lib::DHMap<Kernel::TermList*, Lib::List<IndexEntry*>*> SIndex;

  Lib::DHMap<unsigned, SIndex*> _sIndexes;
  Kernel::Ordering &_ord;
};

}

#endif
