/**
 * @file SplittingFSE.hpp
 * Defines class SplittingFSE.
 */


#ifndef __SplittingFSE__
#define __SplittingFSE__

#include "../Forwards.hpp"

#include "../Lib/DHMap.hpp"

#include "../Indexing/ClauseVariantIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;

class SplittingFSE
: public ForwardSimplificationEngine
{
public:
  void perform(Clause* cl, bool& keep, ClauseIterator& toAdd, ClauseIterator& premises);
private:
  DHMap<Clause*, int, PtrIdentityHash> _clauseNames;
  ClauseVariantIndex _variantIndex;
};

};

#endif /* __SplittingFSE__ */
