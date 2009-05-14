/**
 * @file Spliter.hpp
 * Defines class Spliter.
 */


#ifndef __Spliter__
#define __Spliter__

#include "../Forwards.hpp"

#include "../Lib/DHMap.hpp"

#include "../Indexing/ClauseVariantIndex.hpp"

namespace Kernel {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;

class Spliter
: public ForwardSimplificationEngine
{
public:
  void perform(Clause* cl, bool& keep, ClauseIterator& toAdd, ClauseIterator& premises);
private:
  DHMap<Clause*, int, PtrIdentityHash> _clauseNames;
  ClauseVariantIndex _variantIndex;
};

};

#endif /* __Spliter__ */
