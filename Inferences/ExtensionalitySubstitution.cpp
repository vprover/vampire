/**
 * @file ExtensionalitySubstitution.cpp
 * Implements class ExtensionalitySubstitution.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/SortHelper.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "ExtensionalitySubstitution.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

struct ExtensionalitySubstitution::MatchingSortFn
{
  MatchingSortFn(Literal* lit)
  : _sort(SortHelper::getEqualityArgumentSort(lit)) {}
  DECL_RETURN_TYPE(bool);
  bool operator()(ExtensionalityClause extCl)
  {
    return extCl._sort == _sort;
  }
private:
  unsigned _sort;
};

struct ExtensionalitySubstitution::SubstitutionsFn
{
  SubstitutionsFn (ExtensionalitySubstitution& parent)
  : _parent(parent) {}
  DECL_RETURN_TYPE(VirtualIterator<pair<Literal*, ExtensionalityClause> >);
  OWN_RETURN_TYPE operator()(Literal* lit)
  {
    if(!lit->isEquality() || lit->isPositive()) {
      return OWN_RETURN_TYPE::getEmpty();
    }
    
    return pvi(
      pushPairIntoRightIterator(
	lit,
	getFilteredIterator(
	  _parent._salg->extensionalityClauses(),
	  MatchingSortFn(lit))));
  }
private:
  ExtensionalitySubstitution& _parent;
};

struct ExtensionalitySubstitution::ResultFn
{
  ResultFn(Clause* cl) : _cl(cl) {}
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(pair<Literal*, ExtensionalityClause> arg)
  {
    ExtensionalityClause extCl = arg.second;
    Literal* trmEq = arg.first;
    Literal* varEq = extCl._literal;
    
    // TODO:
    // 1. unify varEq and trmEq
    // 2. build result clause

    NOT_IMPLEMENTED;
    
    return 0;
  }
private:
  Clause* _cl;
};

ClauseIterator ExtensionalitySubstitution::generateClauses(Clause* premise)
{
  CALL("ExtensionalitySubstitution::generateClauses");

  return pvi(
    getMappingIterator(
      getMapAndFlattenIterator(
	Clause::Iterator(*premise),
	SubstitutionsFn(*this)),
      ResultFn(premise)));
}

}
