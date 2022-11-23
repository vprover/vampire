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
 * @file TypeSubstitutionTree.cpp
 * Implements class TypeSubstitutionTree.
 */

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Random.hpp"
#include "Lib/SmartPtr.hpp"

#include "Kernel/TermIterators.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Shell/Options.hpp"

#include "TypeSubstitutionTree.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

TypeSubstitutionTree::TypeSubstitutionTree()
: SubstitutionTree()
{
}

void TypeSubstitutionTree::insert(TermList sort, LeafData ld)
{
  CALL("TypeSubstitutionTree::insert");
  handleTerm(sort,ld,true);
}

void TypeSubstitutionTree::remove(TermList sort, LeafData ld)
{
  CALL("TypeSubstitutionTree::remove");
  handleTerm(sort,ld,false);
}

struct TypeSubstitutionTree::VarUnifFn
{
  VarUnifFn(TermList queryTerm, TermList sort)
  : _queryTerm(queryTerm), _sort(sort) {
    _subst=RobSubstitutionSP(new RobSubstitution());
  }

  TermQueryResult operator() (TermQueryResult tqr) {
    //TODO unnecessary work here. We had the sort and then lost it
    TermList tqrSort = SortHelper::getTermSort(tqr.term, tqr.literal);
    _subst->reset();

    ASS(_sort.isVar() || tqrSort.isVar());
    ALWAYS(_subst->unify(_sort, SubstitutionTree::QRS_QUERY_BANK, tqrSort, SubstitutionTree::QRS_RESULT_BANK));
    
    bool isTypeSub = false;
    if(_queryTerm.isVar() || tqr.term.isVar()){
      ALWAYS(_subst->unify(_queryTerm, SubstitutionTree::QRS_QUERY_BANK, tqr.term, SubstitutionTree::QRS_RESULT_BANK));
    } else {
      isTypeSub = true;
    }

    return TermQueryResult(tqr.term, tqr.literal, tqr.clause,
    ResultSubstitution::fromSubstitution(_subst.ptr(),
      SubstitutionTree::QRS_QUERY_BANK,SubstitutionTree::QRS_RESULT_BANK), isTypeSub);
  }

private:
  RobSubstitutionSP _subst;
  TermList _queryTerm;
  TermList _sort;
};

struct TypeSubstitutionTree::ToTypeSubFn
{

  ToTypeSubFn(TermList queryTerm)
  : _queryTerm(queryTerm) {}

  TermQueryResult operator() (TermQueryResult tqr) {
    if(!_queryTerm.isVar() && !tqr.term.isVar()){
      tqr.isTypeSub = true;
    } else {
      RobSubstitution* subst = tqr.substitution->tryGetRobSubstitution();
      ALWAYS(subst->unify(_queryTerm, SubstitutionTree::QRS_QUERY_BANK, tqr.term, SubstitutionTree::QRS_RESULT_BANK));      
    }
    return tqr;
  }

private:
  TermList _queryTerm;
};

/**
 * According to value of @b insert, insert or remove term.
 */
void TypeSubstitutionTree::handleTerm(TermList sort, LeafData ld, bool insert)
{
  CALL("TypeSubstitutionTree::handleTerm");

  if(sort.isOrdinaryVar()) {
    if(insert) {
      _vars.insert(ld);
    } else {
      // why is this case needed?
      _vars.remove(ld);
    }
  }  else {
    ASS(sort.isTerm());
    Term* term=sort.term();

    Renaming normalizer;
    normalizer.normalizeVariables(ld.term);

    Term* normSort=normalizer.apply(term);

    BindingMap svBindings;
    svBindings.insert(0, TermList(normSort));
    _nextVar = max(_nextVar, 1);

    if(insert) {
      SubstitutionTree::insert(svBindings, ld);
    } else {
      SubstitutionTree::remove(svBindings, ld);
    }
  }
}

//TODO use sorts and delete non-shared
TermQueryResultIterator TypeSubstitutionTree::getUnifications(TermList sort, TermList trm,
	  bool retrieveSubstitutions)
{
  CALL("TypeSubstitutionTree::getUnifications");
 
  auto it1 = !_vars.isEmpty() ? pvi(getMappingIterator(ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), sort, false, /* withConstraints */ false), VarUnifFn(trm, sort))) :
             TermQueryResultIterator::getEmpty();

  if(sort.isOrdinaryVar()) { //TODO return vars as well?
    ASSERTION_VIOLATION_REP("TODO")
    // auto it2 = getMappingIterator(getAllUnifyingIterator(sort,false), VarUnifFn(trm, sort));
    // return pvi(getConcatenatedIterator(it1, it2)); 
  } else {
    ASS(sort.isTerm());
    auto it2 =  getMappingIterator(
	  getResultIterator<UnificationsIterator>(sort.term(), retrieveSubstitutions), ToTypeSubFn(trm));
    return pvi(getConcatenatedIterator(it1, it2));     
  }
}

template<class Iterator>
TermQueryResultIterator TypeSubstitutionTree::getResultIterator(Term* trm,
	  bool retrieveSubstitutions)
{
  return SubstitutionTree::iterator<Iterator>(trm, retrieveSubstitutions, 
       /* withConstraints */ false, 
       /* extra */ false, 
       /* functionalSubtermMap */ nullptr);
}

}
