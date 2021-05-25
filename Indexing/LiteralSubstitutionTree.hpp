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
 * @file LiteralSubstitutionTree.hpp
 * Defines class LiteralSubstitutionTree.
 */


#ifndef __LiteralSubstitutionTree__
#define __LiteralSubstitutionTree__

#include "LiteralIndexingStructure.hpp"
#include "SubstitutionTree.hpp"

namespace Indexing {

class LiteralSubstitutionTree
: public LiteralIndexingStructure, SubstitutionTree
{
public:
  CLASS_NAME(LiteralSubstitutionTree);
  USE_ALLOCATOR(LiteralSubstitutionTree);

  LiteralSubstitutionTree(bool useC=false);

  void insert(Literal* lit, Clause* cls);
  void remove(Literal* lit, Clause* cls);
  void handleLiteral(Literal* lit, Clause* cls, bool insert);

  SLQueryResultIterator getAll();

  SLQueryResultIterator getUnifications(Literal* lit,
	  bool complementary, bool retrieveSubstitutions);

  SLQueryResultIterator getUnificationsWithConstraints(Literal* lit,
          bool complementary, bool retrieveSubstitutions);

  SLQueryResultIterator getGeneralizations(Literal* lit,
	  bool complementary, bool retrieveSubstitutions);

  SLQueryResultIterator getInstances(Literal* lit,
	  bool complementary, bool retrieveSubstitutions);

  SLQueryResultIterator getVariants(Literal* lit,
	  bool complementary, bool retrieveSubstitutions);

#if VDEBUG
  virtual void markTagged(){ SubstitutionTree::markTagged();}
  vstring toString() {return SubstitutionTree::toString();}
#endif

private:
  struct SLQueryResultFunctor;
  struct LDToSLQueryResultFn;
  struct LDToSLQueryResultWithSubstFn;
  struct UnifyingContext;
  struct PropositionalLDToSLQueryResultWithSubstFn;
  struct LeafToLDIteratorFn;

  template <bool instantiation>
  struct MatchingFilter
  {
    MatchingFilter(Literal* queryLit, bool retrieveSubstitutions)
    : _queryEqSort(SortHelper::getEqualityArgumentSort(queryLit)),
      _isTwoVarEq(queryLit->isTwoVarEquality()),
      _retrieveSubstitutions(retrieveSubstitutions) {}

    bool enter(const SLQueryResult& res)
    {
      CALL("LiteralSubstitutionTree::MatchingFilter::enter()");
      ASS(res.literal->isEquality());
    
      if(instantiation){
        //if the query lit isn't a two variable equality, sort unification
        //is guranteed via term unification
        if(!_isTwoVarEq){ return true; }
      } else {
        //generaisation
        if(!res.literal->isTwoVarEquality()){ return true; }
      }

      TermList resSort = SortHelper::getEqualityArgumentSort(res.literal);
      if(_retrieveSubstitutions) {
        return instantiation ? res.substitution->matchSorts(_queryEqSort, resSort) 
                             : res.substitution->matchSorts(resSort, _queryEqSort); 
      } else {
        static RobSubstitution subst;
        subst.reset();
        return instantiation ? subst.match(_queryEqSort, 0, resSort, 1):
                               subst.match(resSort, 0, _queryEqSort, 1);           
      }
    }

    //dummy. UnificationFilter needs a leave function to undo the sort unification.
    //MatchingFilter doesn't require this, since the sort unifier is added onto
    //the final term unifier and undone by the next call to backTrack() in FastGen 
    //or FastInst iterator.
    void leave(const SLQueryResult& res){  }
  private:
    TermList _queryEqSort;
    bool _isTwoVarEq;
    bool _retrieveSubstitutions;
  };

  template <bool polymorphic>
  struct UnificationFilter
  {
    UnificationFilter(Literal* queryLit, bool retrieveSubstitutions)
    : _queryEqSort(SortHelper::getEqualityArgumentSort(queryLit)), 
      _retrieveSubs(retrieveSubstitutions) {}

    bool enter(const SLQueryResult& res)
    {
      CALL("LiteralSubstitutionTree::UnificationFilter::enter()");
      ASS(res.literal->isEquality());
      
      //the polymorphism check isn't strictly necessary. However, if it wasn't
      //included, on monomorphic problems we would be using unification to check
      //whether two constant are identical

      TermList resSort = SortHelper::getEqualityArgumentSort(res.literal);
      if(!polymorphic){
        return _queryEqSort == resSort;
      } else if(_retrieveSubs){
        RobSubstitution* subst = res.substitution->tryGetRobSubstitution();
        ASS(subst);
        subst->bdRecord(_bdataEq);
        bool success = subst->unify(_queryEqSort, 0, resSort, 1);
        subst->bdDone();
        if(!success){
          _bdataEq.backtrack();
        }
        return success;
      } else {
        static RobSubstitution subst;
        subst.reset();
        return subst.unify(_queryEqSort, 0, resSort, 1);
      }
    }

    void leave(const SLQueryResult& res){
      CALL("LiteralSubstitutionTree::UnificationFilter::leave()");
      if(_retrieveSubs && polymorphic){
        _bdataEq.backtrack();
        ASS(_bdataEq.isEmpty());
      }
    }
  private:
    TermList _queryEqSort;
    bool _retrieveSubs;
    BacktrackData _bdataEq;
  };

  template<class Iterator, class Filter>
  SLQueryResultIterator getResultIterator(Literal* lit,
	  bool complementary, bool retrieveSubstitutions, bool useConstraints);

  unsigned getRootNodeIndex(Literal* t, bool complementary=false);
  bool _polymorphic;
};

};

#endif /* __LiteralSubstitutionTree__ */
