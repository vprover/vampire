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
#include "Kernel/ColorHelper.hpp"

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
  VirtualIterator<pair<Literal*, ExtensionalityClause> > operator()(Literal* lit)
  {
    CALL("ExtensionalityResolution::ForwardPairingFn::operator()");
    
    if (!lit->isEquality() || lit->isPositive()) {
      return VirtualIterator<pair<Literal*, ExtensionalityClause> >::getEmpty();
    }

    TermList s = SortHelper::getEqualityArgumentSort(lit);
    
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
  VirtualIterator<pair<pair<Literal*, ExtensionalityClause>, RobSubstitution*> > operator()(pair<Literal*, ExtensionalityClause> arg)
  {
    CALL("ExtensionalityResolution::ForwardUnificationsFn::operator()");
    
    Literal* trmEq = arg.first;
    Literal* varEq = arg.second.literal;

    SubstIterator unifs = _subst->unifiers(varEq,0,trmEq,1,true);
    if (!unifs.hasNext()) {
      return VirtualIterator<pair<pair<Literal*, ExtensionalityClause>, RobSubstitution*> >::getEmpty();
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
  ForwardResultFn(Clause* otherCl, ExtensionalityResolution& parent) : _otherCl(otherCl), _parent(parent) {}
  Clause* operator()(pair<pair<Literal*, ExtensionalityClause>, RobSubstitution*> arg)
  {
    CALL("ExtensionalityResolution::ForwardResultFn::operator()");
    
    RobSubstitution* subst = arg.second;
    Literal* otherLit = arg.first.first;
    Clause* extCl = arg.first.second.clause;
    Literal* extLit = arg.first.second.literal;

    return performExtensionalityResolution(extCl, extLit, _otherCl, otherLit, subst,
                                             env.statistics->forwardExtensionalityResolution,
                                             _parent.getOptions());
  }
private:
  Clause* _otherCl;
  ExtensionalityResolution& _parent;
};

/////////////////   Backward Extensionality   //////////////////////

/**
 * Functor for filtering negative equality literals of particular sort.
 */
struct ExtensionalityResolution::NegEqSortFn
{
  NegEqSortFn (TermList sort) : _sort(sort) {}
  bool operator()(Literal* lit)
  {
    CALL("ExtensionalityResolution::NegEqSortFn::operator()");
    
    return lit->isEquality() && lit->isNegative() &&
      SortHelper::getEqualityArgumentSort(lit) == _sort;
  }
private:
  TermList _sort;
};

/**
 * Functor for filtering selected negative literals of particular sort (the sort
 * of the given extensionality clause) in active clauses.
 */
struct ExtensionalityResolution::BackwardPairingFn
{
  BackwardPairingFn (TermList sort) : _sort(sort) {}
  VirtualIterator<pair<Clause*, Literal*> > operator()(Clause* cl)
  {
    CALL("ExtensionalityResolution::BackwardPairingFn::operator()");
    
    return pvi(pushPairIntoRightIterator(
        cl,
        getFilteredIterator(
          cl->getSelectedLiteralIterator(),
          NegEqSortFn(_sort))));
  }
private:
  TermList _sort;
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
  VirtualIterator<pair<pair<Clause*, Literal*>, RobSubstitution*> > operator()(pair<Clause*, Literal*> arg)
  {
    CALL("ExtensionalityResolution::BackwardUnificationsFn::operator()");
    
    Literal* otherLit = arg.second;
    
    SubstIterator unifs = _subst->unifiers(_extLit,0,otherLit,1,true);
    if (!unifs.hasNext()) {
      return VirtualIterator<pair<pair<Clause*, Literal*>, RobSubstitution*> >::getEmpty();
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
  BackwardResultFn(Clause* extCl, Literal* extLit, ExtensionalityResolution& parent) : _extCl(extCl), _extLit(extLit), _parent(parent) {}
  Clause* operator()(pair<pair<Clause*, Literal*>, RobSubstitution*> arg)
  {
    CALL("ExtensionalityResolution::BackwardResultFn::operator()");
    
    RobSubstitution* subst = arg.second;
    Clause* otherCl = arg.first.first;
    Literal* otherLit = arg.first.second;

    return performExtensionalityResolution(_extCl, _extLit, otherCl, otherLit, subst,
                                             env.statistics->backwardExtensionalityResolution,
                                             _parent.getOptions());
  }
private:
  Clause* _extCl;
  Literal* _extLit;
  ExtensionalityResolution& _parent;
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
  unsigned& counter,
  const Options& opts)
{
  CALL("ExtensionalityResolution::performExtensionalityResolution");
  
  if(!ColorHelper::compatible(extCl->color(),otherCl->color()) ) {
    env.statistics->inferencesSkippedDueToColors++;
    if(opts.showBlocked()) {
      env.beginOutput();
      env.out()<<"Blocked extensionality resolution of "<<extCl->toString()<<" and "<<otherCl->toString()<<endl;
      env.endOutput();
    }
    return 0;
  }

  unsigned extLen = extCl->length();
  unsigned otherLen = otherCl->length();
  
  unsigned newLength = otherLen + extLen - 2;
  Clause* res = new(newLength) Clause(newLength, GeneratingInference2(InferenceRule::EXTENSIONALITY_RESOLUTION, extCl, otherCl));

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
    // Get all <clause,literal> pairs, where clause is an active clause
    // and literal a negative equality in clause of same sort as the given
    // extensionality clause.
    auto it1 =
        getMapAndFlattenIterator(
          // (possible) TODO: We do not actually maintain a set neg_equal of
          // active clauses having a negative selected equality literal as
          // described in the extensionality resolution paper. Instead we
          // iterate the active clauses every time a backward extensionality
          // resolution inference has to be performed under the assumption
          // that this happens rarely. Experiments could clarify, which
          // solution is more efficient.
          _salg->activeClauses(),
          BackwardPairingFn(extLit->twoVarEqSort()));

    // For each <clause,literal> pair, we get 2 substitutions (by unifying
    // X=Y from given extensionality clause and literal.
    // Elements: <<clause,literal>,subst>
    auto it2 = getMapAndFlattenIterator(it1,BackwardUnificationsFn(extLit));

    // Construct result clause by applying substitution.
    auto it3 = getMappingIterator(it2,BackwardResultFn(premise, extLit, *this));

    // filter out only non-zero results
    auto it4 = getFilteredIterator(it3, NonzeroFn());

    backwardIterator = pvi(it4);
  } else {
    backwardIterator = ClauseIterator::getEmpty();
  }
  
  // For each selected negative equality in given clause, find all
  // active extensionality clauses of same sort.
  // Elements: <literal,extClause>
  auto it1 = getMapAndFlattenIterator(premise->getSelectedLiteralIterator(),ForwardPairingFn(extClauses));

  // For each <literal,extClause> pair, we get 2 substitutions (by
  // unifying literal and extClause.literal, i.e. the variable equality in
  // extensionality clause).
  // Elements: <<literal,extClause>,subst>
  auto it2 = getMapAndFlattenIterator(it1,ForwardUnificationsFn());

  // Construct result clause by applying substitution.
  auto it3 = getMappingIterator(it2,ForwardResultFn(premise, *this));

  // filter out only non-zero results
  auto it4 = getFilteredIterator(it3, NonzeroFn());

  // Concatenate results from forward extensionality and (above constructed)
  // backward extensionality.
  auto it5 = getConcatenatedIterator(it4,backwardIterator);

  return pvi(it5);
}
