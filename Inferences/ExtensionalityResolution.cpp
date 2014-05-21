/**
 * @file ExtensionalityResolution.cpp
 * Implements class ExtensionalityResolution.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "ExtensionalityResolution.hpp"

using namespace Inferences;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

/////////////////   Forward Extensionality   //////////////////////

/**
 * Functor for pairing negative selected literals of the given clause with all
 * sort-matching extensionality clauses for forward extensionality inferences.
 * @since 05/01/2014
 * @author Bernhard Kragl
 */
struct ExtensionalityResolution::ForwardPairingFn
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
struct ExtensionalityResolution::ForwardUnificationsFn
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
struct ExtensionalityResolution::ForwardResultFn
{
  ForwardResultFn(Clause* otherCl) : _otherCl(otherCl) {}
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(pair<pair<Literal*, ExtensionalityClause>, RobSubstitution*> arg)
  {
    RobSubstitution* subst = arg.second;
    Literal* otherLit = arg.first.first;
    Clause* extCl = arg.first.second.clause;
    Literal* extLit = arg.first.second.literal;

    return performExtensionalityResolution(extCl, extLit, _otherCl, otherLit, subst,
                                             env.statistics->forwardExtensionalityResolution);
  }
private:
  Clause* _otherCl;
};

/////////////////   Backward Extensionality   //////////////////////

/**
 * Functor for filtering negative equality literals of particular sort.
 */
struct ExtensionalityResolution::NegEqSortFn
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
struct ExtensionalityResolution::BackwardPairingFn
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
struct ExtensionalityResolution::BackwardUnificationsFn
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
struct ExtensionalityResolution::BackwardResultFn
{
  BackwardResultFn(Clause* extCl, Literal* extLit) : _extCl(extCl), _extLit(extLit) {}
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(pair<pair<Clause*, Literal*>, RobSubstitution*> arg)
  {
    RobSubstitution* subst = arg.second;
    Clause* otherCl = arg.first.first;
    Literal* otherLit = arg.first.second;

    return performExtensionalityResolution(_extCl, _extLit, otherCl, otherLit, subst,
                                             env.statistics->backwardExtensionalityResolution);
  }
private:
  Clause* _extCl;
  Literal* _extLit;
};

/////////////////   Extensionality   //////////////////////

/**
 * Generate clause by applying @c subst to all literals of @c extCl (except @c
 * extLit) and all literals of @c otherCl (except @c otherLit).
 */
Clause* ExtensionalityResolution::performExtensionalityResolution(
  Clause* extCl, Literal* extLit,
  Clause* otherCl, Literal* otherLit,
  RobSubstitution* subst,
  unsigned& counter)
{
  unsigned extLen = extCl->length();
  unsigned otherLen = otherCl->length();
  
  unsigned newLength = otherLen + extLen - 2;
  Unit::InputType newInputType = Unit::getInputType(extCl->inputType(), otherCl->inputType());
  Inference* inf = new Inference2(Inference::EXTENSIONALITY_RESOLUTION, extCl, otherCl);
  Clause* res = new(newLength) Clause(newLength, newInputType, inf);

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
  counter++;
  
  TRACE("inf_ext", tout
        << "extensionality inference" << endl
        << "ExtCl: " << extCl->toString() << endl
        << "OthCl: " << otherCl->toString() << endl
        << "Res:   " << res->toString() << endl;
    );
  
  return res;
}
  
/**
 * Construct iterator, returning the results for forward and backward
 * extensionality on @c premise.
 */
ClauseIterator ExtensionalityResolution::generateClauses(Clause* premise)
{
  CALL("ExtensionalityResolution::generateClauses");

  ExtensionalityClauseContainer* extClauses = _salg->getExtensionalityClauseContainer();
  ClauseIterator backwardIterator;

  Literal* extLit = extClauses->addIfExtensionality(premise);
  
  if (extLit) {
    // Note: read comments inside out.
    backwardIterator = pvi(
      // Construct result clause by applying substitution.
      getMappingIterator(
        // For each <clause,literal> pair, we get 2 substitutions (by unifying
        // X=Y from given extensionality clause and literal.
        // Elements: <<clause,literal>,subst>
        getMapAndFlattenIterator(
          // Get all <clause,literal> pairs, where clause is an active clause
          // and literal a negative equality in clause of same sort as the given
          // extensionality clause.
          getMapAndFlattenIterator(
            _salg->activeClauses(),
            BackwardPairingFn(extLit->twoVarEqSort())),
          BackwardUnificationsFn(extLit)),
        BackwardResultFn(premise, extLit)));
  } else {
    backwardIterator = ClauseIterator::getEmpty();
  }
  
  // Note: read comments inside out.
  return pvi(
    // Concatenate results from forward extensionality and (above constructed)
    // backward extensionality.
    getConcatenatedIterator(
      // Construct result clause by applying substitution.
      getMappingIterator(
        // For each <literal,extClause> pair, we get 2 substitutions (by
        // unifying literal and extClause.literal, i.e. the variable equality in
        // extensionality clause).
        // Elements: <<literal,extClause>,subst>
        getMapAndFlattenIterator(
          // For each selected negative equality in given clause, find all
          // active extensionality clauses of same sort.
          // Elements: <literal,extClause>
          getMapAndFlattenIterator(
            premise->getSelectedLiteralIterator(),
            ForwardPairingFn(_salg->getExtensionalityClauseContainer())),
          ForwardUnificationsFn()),
        ForwardResultFn(premise)),
      backwardIterator));
} 
