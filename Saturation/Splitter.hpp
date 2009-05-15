/**
 * @file Splitter.hpp
 * Defines class Splitter.
 */


#ifndef __Splitter__
#define __Splitter__

#include "../Forwards.hpp"

#include "../Lib/DHMap.hpp"

#include "../Indexing/ClauseVariantIndex.hpp"

namespace Saturation {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;

class Splitter
{
public:
  void doSplitting(Clause* cl, ClauseIterator& newComponents, ClauseIterator& modifiedComponents);
private:
  void handleNoSplit(Clause* cl, ClauseIterator& newComponents,
		ClauseIterator& modifiedComponents);

  DHMap<Clause*, int, PtrIdentityHash> _clauseNames;
  ClauseVariantIndex _variantIndex;
};

};

#endif /* __Splitter__ */
