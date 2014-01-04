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
#include "Kernel/RobSubstitution.hpp"
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

/**
 * Functor, computing if an extensionality clause has the same sort as some
 * given literal.
 */
struct ExtensionalitySubstitution::MatchingSortFn
{
  MatchingSortFn(Literal* lit)
  : _sort(SortHelper::getEqualityArgumentSort(lit)) {}
  DECL_RETURN_TYPE(bool);
  bool operator()(ExtensionalityClause extCl)
  {
    return extCl.sort == _sort;
  }
private:
  unsigned _sort;
};

/**
 * Given a literal, this functor returns all extensionality clauses which can be
 * used in extensionality inference.
 */
struct ExtensionalitySubstitution::PairingFn
{
  PairingFn (ExtensionalitySubstitution& parent)
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

/**
 * This functor computes the unifications between the positive equality of an
 * extensionality clause and the matching negative equality in the given clause.
 */
struct ExtensionalitySubstitution::UnificationsFn
{
  UnificationsFn() { _subst = RobSubstitutionSP(new RobSubstitution()); }
  DECL_RETURN_TYPE(VirtualIterator<pair<pair<Literal*, ExtensionalityClause>, RobSubstitution*> >);
  OWN_RETURN_TYPE operator()(pair<Literal*, ExtensionalityClause> arg)
  {
    Literal* trmEq = arg.first;
    Literal* varEq = arg.second.literal;

    SubstIterator unifs = _subst->unifiers(varEq,0,trmEq,1,true);
    if(!unifs.hasNext()) {
      return OWN_RETURN_TYPE::getEmpty();
    }
    return pvi(pushPairIntoRightIterator(arg, unifs));
  }
private:
  RobSubstitutionSP _subst;
};

/**
 * Generate the result clause of an extensionality inference.
 */
struct ExtensionalitySubstitution::ResultFn
{
  ResultFn(Clause* cl) : _cl(cl), _cLen(cl->length()) {}
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(pair<pair<Literal*, ExtensionalityClause>, RobSubstitution*> arg)
  {
    RobSubstitution* subst = arg.second;
    Literal* skipLitGiven = arg.first.first;
    Literal* skipLitExt = arg.first.second.literal;
    Clause* extCl = arg.first.second.clause;
    unsigned extLen = extCl->length();

    unsigned newLength = _cLen + extLen - 2;
    Inference* inf = new Inference2(Inference::EXTENSIONALITY_SUBSTITUTION, extCl, _cl);
    Clause* res = new(newLength) Clause(newLength, _cl->inputType(), inf);

    unsigned next = 0;

    for(unsigned i = 0; i < extLen; i++) {
      Literal* curr = (*extCl)[i];
      if(curr != skipLitExt) {
	(*res)[next++] = subst->apply(curr, 0);
      }
    }

    for(unsigned i = 0; i < _cLen; i++) {
      Literal* curr = (*_cl)[i];
      if(curr != skipLitGiven) {
	(*res)[next++] = subst->apply(curr, 1);
      }
    }
    
    ASS_EQ(next,newLength);

    cout << subst->toString(true) << endl;
    cout << extCl->toString() << endl
	 << _cl->toString() << endl
	 << res->toString() << endl;

    return res;
  }
private:
  Clause* _cl;
  unsigned _cLen;
};
  
ClauseIterator ExtensionalitySubstitution::generateClauses(Clause* premise)
{
  CALL("ExtensionalitySubstitution::generateClauses");

  return pvi(
    getMappingIterator(
      getMapAndFlattenIterator(
	getMapAndFlattenIterator(
	  Clause::Iterator(*premise),
	  PairingFn(*this)),
	UnificationsFn()),
      ResultFn(premise)));
}

}
