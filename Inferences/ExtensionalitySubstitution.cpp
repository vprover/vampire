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
// AV: why do you include ColorHelper here? 
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

using namespace Inferences;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

/////////////////   Forward Extensionality   //////////////////////

/**
 * Functor for pairing negative selected literals of the given clause with all
 * sort-matching extensionality clauses for forward extensionality inferences.
 AV: comments, see below
 * @since 05/01/2014
 * @author Bernhard Kragl
 */
struct ExtensionalitySubstitution::ForwardPairingFn
{
  ForwardPairingFn (ExtensionalityClauseContainer* extClauses)
  : _extClauses(extClauses) {}
  DECL_RETURN_TYPE(VirtualIterator<pair<Literal*, ExtensionalityClause> >);
  OWN_RETURN_TYPE operator()(Literal* lit)
  {
    if (!lit->isEquality() || lit->isPositive()) {
      return OWN_RETURN_TYPE::getEmpty();
    }

    unsigned s = SortHelper::getEqualityArgumentSort(lit);
    
    return pvi(
      pushPairIntoRightIterator(
        lit,
        _extClauses->activeIterator(s)));
  }
private:
  ExtensionalityClauseContainer* _extClauses;
};

/**
 * This functor computes the unifications between the positive equality of an
 * extensionality clause and the matching negative equality in the given clause.
 */
struct ExtensionalitySubstitution::ForwardUnificationsFn
{
  ForwardUnificationsFn() { _subst = RobSubstitutionSP(new RobSubstitution()); }
  DECL_RETURN_TYPE(VirtualIterator<pair<pair<Literal*, ExtensionalityClause>, RobSubstitution*> >);
  OWN_RETURN_TYPE operator()(pair<Literal*, ExtensionalityClause> arg)
  {
    Literal* trmEq = arg.first;
    Literal* varEq = arg.second.literal;

    SubstIterator unifs = _subst->unifiers(varEq,0,trmEq,1,true);
    if (!unifs.hasNext()) {
      return OWN_RETURN_TYPE::getEmpty();
    }
    return pvi(pushPairIntoRightIterator(arg, unifs));
  }
private:
  RobSubstitutionSP _subst;
};

/**
 * Generate the result clause of a forward extensionality inference.
 */
struct ExtensionalitySubstitution::ForwardResultFn
{
  ForwardResultFn(Clause* otherCl) : _otherCl(otherCl) {}
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(pair<pair<Literal*, ExtensionalityClause>, RobSubstitution*> arg)
  {
    RobSubstitution* subst = arg.second;
    Literal* otherLit = arg.first.first;
    Clause* extCl = arg.first.second.clause;
    Literal* extLit = arg.first.second.literal;

    return performExtensionalitySubstitution(extCl, extLit, _otherCl, otherLit, subst);
  }
private:
  Clause* _otherCl;
};

/////////////////   Backward Extensionality   //////////////////////

/**
 * Functor for filtering negative equality literals of particular sort.
 */
struct ExtensionalitySubstitution::NegEqSortFn
{
  NegEqSortFn (unsigned sort) : _sort(sort) {}
  DECL_RETURN_TYPE(bool);
  OWN_RETURN_TYPE operator()(Literal* lit)
  {
    return lit->isEquality() && lit->isNegative() &&
      SortHelper::getEqualityArgumentSort(lit) == _sort;
  }
private:
  unsigned _sort;
};

/**
 * Functor for filtering selected negative literals of particular sort (the sort
 * of the given extensionality clause) in active clauses.
 */
struct ExtensionalitySubstitution::BackwardPairingFn
{
  BackwardPairingFn (unsigned sort) : _sort(sort) {}
  DECL_RETURN_TYPE(VirtualIterator<pair<Clause*, Literal*> >);
  OWN_RETURN_TYPE operator()(Clause* cl)
  {
    return pvi(pushPairIntoRightIterator(
        cl,
        getFilteredIterator(
          cl->getSelectedLiteralIterator(),
          NegEqSortFn(_sort))));
  }
private:
  unsigned _sort;
};

/**
 * This functor computes the unifications between the positive equality of the
 * given extensionality clause and a matching negative equality in some active
 * clause.
 */
struct ExtensionalitySubstitution::BackwardUnificationsFn
{
  BackwardUnificationsFn(Literal* extLit)
  : _extLit (extLit) { _subst = RobSubstitutionSP(new RobSubstitution()); }
  DECL_RETURN_TYPE(VirtualIterator<pair<pair<Clause*, Literal*>, RobSubstitution*> >);
  OWN_RETURN_TYPE operator()(pair<Clause*, Literal*> arg)
  {
    Literal* otherLit = arg.second;
    
    SubstIterator unifs = _subst->unifiers(_extLit,0,otherLit,1,true);
    if (!unifs.hasNext()) {
      return OWN_RETURN_TYPE::getEmpty();
    }
    return pvi(pushPairIntoRightIterator(arg, unifs));
  }
private:
  Literal* _extLit;
  RobSubstitutionSP _subst;
};

/**
 * Generate the result clause of a backward extensionality inference.
 */
struct ExtensionalitySubstitution::BackwardResultFn
{
  BackwardResultFn(Clause* extCl, Literal* extLit) : _extCl(extCl), _extLit(extLit) {}
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(pair<pair<Clause*, Literal*>, RobSubstitution*> arg)
  {
    RobSubstitution* subst = arg.second;
    Clause* otherCl = arg.first.first;
    Literal* otherLit = arg.first.second;

    return performExtensionalitySubstitution(_extCl, _extLit, otherCl, otherLit, subst);
  }
private:
  Clause* _extCl;
  Literal* _extLit;
};

/////////////////   Extensionality   //////////////////////

Clause* ExtensionalitySubstitution::performExtensionalitySubstitution(
  Clause* extCl, Literal* extLit,
  Clause* otherCl, Literal* otherLit,
  RobSubstitution* subst)
{
  unsigned extLen = extCl->length();
  unsigned otherLen = otherCl->length();
  
  unsigned newLength = otherLen + extLen - 2;
  Unit::InputType newInputType = Unit::getInputType(extCl->inputType(), otherCl->inputType());
  Inference* inf = new Inference2(Inference::EXTENSIONALITY_SUBSTITUTION, extCl, otherCl);
  Clause* res = new(newLength) Clause(newLength, newInputType, inf);
  // BK: Should new weight be computed like in superposition? Which statistics to keep?

  unsigned next = 0;

  for(unsigned i = 0; i < extLen; i++) {
    Literal* curr = (*extCl)[i];
    if (curr != extLit) {
      (*res)[next++] = subst->apply(curr, 0);
    }
  }

  for(unsigned i = 0; i < otherLen; i++) {
    Literal* curr = (*otherCl)[i];
    if (curr != otherLit) {
      (*res)[next++] = subst->apply(curr, 1);
    }
  }
    
  ASS_EQ(next,newLength);

  //cout << subst->toString(true) << endl;
  /*cout << "######################" << endl
       << extCl->toString() << endl
       << otherCl->toString() << endl
       << res->toString() << endl;*/

  return res;
}
  
// AV: comments?
ClauseIterator ExtensionalitySubstitution::generateClauses(Clause* premise)
{
  CALL("ExtensionalitySubstitution::generateClauses");

  ClauseIterator backwardIterator;
  
  if (premise->isExtensionality()) {
    Literal* extLit;
    for (Clause::Iterator ci(*premise); ci.hasNext(); ) {
      extLit = ci.next();
      // AV: style - all conditionals with parentheses
      if (extLit->isTwoVarEquality() && extLit->isPositive())
        break;
    }

    backwardIterator = pvi(
      getMappingIterator(
        getMapAndFlattenIterator(
          getMapAndFlattenIterator(
            _salg->activeClauses(),
            BackwardPairingFn(extLit->twoVarEqSort())),
          BackwardUnificationsFn(extLit)),
        BackwardResultFn(premise, extLit)));
  } else {
    backwardIterator = ClauseIterator::getEmpty();
  }
  
  // AV: what does this expression do? - comments required
  return pvi(
    getConcatenatedIterator(
      getMappingIterator(
        getMapAndFlattenIterator(
          getMapAndFlattenIterator(
            premise->getSelectedLiteralIterator(),
            ForwardPairingFn(_salg->getExtensionalityClauseContainer())),
          ForwardUnificationsFn()),
        ForwardResultFn(premise)),
      backwardIterator));
} 
