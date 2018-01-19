
/*
 * File TermAlgebraIndex.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file AcyclicityIndex.cpp
 * Implements class AcyclicityIndex
 */

#include "Kernel/Inference.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"

#include "Lib/Backtrackable.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Stack.hpp"

#include "Shell/TermAlgebra.hpp"

#include "TermAlgebraIndex.hpp"

using namespace Kernel;
using namespace Lib;

namespace Indexing
{
  unsigned ChainQueryResult::totalLengthClauses()
  {
    CALL("ChainQueryResult::totalLengthClauses");

    unsigned n = 0;
    List<Clause*>::Iterator it(premises);
    while (it.hasNext()) {
      n += it.next()->length();
    }

    return n;
  }

  void addSubterm(TermList t, List<TermList>*& l)
  {
    CALL("addSubterm");
    List<TermList>::Iterator it(l);
    while (it.hasNext()) {
      // TODO test for unifiability, keep only most general term
      if (TermList::equals(t, it.next())) {
        return;
      }
    }
    List<TermList>::push(t, l);
  }
  
  List<TermList>* AcyclicityIndex::getSubterms(Term *t)
  {
    CALL("AcyclicityIndex::getSubterms");
    
    Stack<Term*> toVisit;
    List<TermList>* res = List<TermList>::empty();
    
    unsigned sort = SortHelper::getResultSort(t);
    ASS(env.signature->isTermAlgebraSort(sort));
    TermAlgebra* ta = env.signature->getTermAlgebraOfSort(sort);

    for (unsigned i = 0; i < t->arity(); i++) {
      if (ta->isMutualTypeSort(SortHelper::getArgSort(t, i))) {
        TermList *s = t->nthArgument(i);
        addSubterm(*s, res);
        if (s->isTerm()) {
          toVisit.push(s->term());
        }
      }
    }

    while (toVisit.isNonEmpty()) {
      Term *u = toVisit.pop();
      if (env.signature->getFunction(u->functor())->termAlgebraCons()) {
        for (unsigned i = 0; i < u->arity(); i++) {
          if (ta->isMutualTypeSort(SortHelper::getArgSort(u, i))) {
            TermList *s = u->nthArgument(i);
            addSubterm(*s, res);
            if (s->isTerm()) {
              toVisit.push(s->term());
            }
          }
        }
      }
    }
    
    return res;
  }

  bool AcyclicityIndex::matchesPattern(Literal *lit, TermList *&fs, TermList *&t, unsigned *sort)
  {
    CALL("AcyclicityIndex::matchesPattern");

    if (!lit->isEquality() || !lit->polarity()) {
      return false;
    }

    *sort = SortHelper::getEqualityArgumentSort(lit);
    if (!env.signature->isTermAlgebraSort(*sort) || env.signature->getTermAlgebraOfSort(*sort)->allowsCyclicTerms()) {
      return false;
    }

    TermList *l = lit->nthArgument(0);
    TermList *r = lit->nthArgument(1);
    
    bool termAlgebraConsL = l->isTerm() && env.signature->getFunction(l->term()->functor())->termAlgebraCons();
    bool termAlgebraConsR = r->isTerm() && env.signature->getFunction(r->term()->functor())->termAlgebraCons();
    
    if (!termAlgebraConsL && termAlgebraConsR) {
      t = l;
      fs = r;
      Ordering::Result o = _ord.getEqualityArgumentOrder(lit);
      return (o == Ordering::INCOMPARABLE || o == Ordering::LESS || o == Ordering::LESS_EQ);
    } else if (termAlgebraConsL && !termAlgebraConsR) {
      fs = l;
      t = r;
      Ordering::Result o = _ord.getEqualityArgumentOrder(lit);
      return (o == Ordering::INCOMPARABLE || o == Ordering::GREATER || o == Ordering::GREATER_EQ);
    } else {
      return false;
    }
  }
  
  struct AcyclicityIndex::IndexEntry {
  public:
    IndexEntry(Literal *l, Clause *c, TermList t, List<TermList>* subterms) :
      lit(l),
      clause(c),
      t(t),
      subterms(subterms)
    {}

    CLASS_NAME(AcyclicityIndex::IndexEntry);
    USE_ALLOCATOR(AcyclicityIndex::IndexEntry);

    Literal* lit;
    Clause* clause;
    TermList t;
    List<TermList>* subterms;
  };

  /* The search algorithm is explained in the paper "An inference rule
     for the acyclicity property of term algebras", where it is
     described as a recursive algorithm, essentially a DFS. Here it is
     implemented non-recursively, with a stack.

     The nodes represent the tree built during the search. There are
     two types of nodes, subterm nodes and unification nodes
     (corresponding to the two static builder methods). An invariant
     of the tree is that a unification node has for parent a subterm
     node, as well as the other way around.

     The root of the tree is a unification node (with the literal that
     the query originates from)
   */
  struct AcyclicityIndex::ChainSearchTreeNode
  {
    ChainSearchTreeNode(TermList t,
                        Literal *l,
                        Clause *c,
                        ChainSearchTreeNode *n,
                        unsigned d,
                        unsigned i,
                        bool b)
      :
      term(t),
      lit(l),
      clause(c),
      parent(n),
      depth(d),
      substIndex(i),
      isUnificationNode(b)
    {}

    static ChainSearchTreeNode *subtermNode(TermList t,
                                            Literal *l,
                                            Clause *c,
                                            ChainSearchTreeNode *n,
                                            unsigned substIndex)
    {
      return new ChainSearchTreeNode(t, l, c, n, n ? n->depth + 1 : 0, substIndex, false);
    }

    static ChainSearchTreeNode *unificationNode(TermList t,
                                                Literal *l,
                                                Clause *c,
                                                ChainSearchTreeNode *n,
                                                unsigned substIndex)
    {
      return new ChainSearchTreeNode(t, l, c, n, n ? n->depth : 0, substIndex, true);
    }

    CLASS_NAME(AcyclicityIndex::ChainSearchTreeNode);
    USE_ALLOCATOR(AcyclicityIndex::ChainSearchTreeNode);

    TermList term;
    Literal *lit;
    Clause *clause;
    ChainSearchTreeNode *parent;
    unsigned depth;
    unsigned substIndex;
    bool isUnificationNode;

  };

  struct AcyclicityIndex::ChainSearchIterator
    : public IteratorCore<ChainQueryResult>
  {
    ChainSearchIterator(Literal *queryLit,
                        Clause *queryClause,
                        AcyclicityIndex& aindex)
      :
      _queryLit(queryLit),
      _queryClause(queryClause),
      _aindex(aindex),
      _nextResult(nullptr),
      _stack(0),
      _subst(new RobSubstitution()),
      _substChanges(0),
      _nextAvailableIndex(0),
      _currentDepth(0)
    {
      CALL("AcyclicityIndex::ChainSearchIterator");

      TermList *t;
      TermList *fs;
      if (_aindex.matchesPattern(queryLit, fs, t, &_querySort)
          && _aindex._lIndex.find(make_pair(queryLit, queryClause))) {
        _queryTerm = TermList(*t);
        IndexEntry *entry = aindex._lIndex.get(make_pair(queryLit, queryClause));
        _stack.push(ChainSearchTreeNode::unificationNode(entry->t,
                                                         queryLit,
                                                         queryClause,
                                                         nullptr,
                                                         _nextAvailableIndex++));
      }
      ASS_EQ(_currentDepth, _substChanges.size());
    }

    ~ChainSearchIterator()
    {
      if (_nextResult) {
        delete _nextResult;
      }
    }
    
    Clause *applySubstitution(Clause *c, unsigned index)
    {
      CALL("AcyclicityIndex::ChainSearchIterator::applySubstitution");
      
      unsigned clen = c->length();
      Inference* inf = new Inference1(Inference::INSTANTIATION, c);
      Clause* res = new(clen) Clause(clen,
                                     c->inputType(),
                                     inf);

      for (unsigned i = 0; i < clen; i++) {
        (*res)[i] = _subst->apply((*c)[i], index);
      }

      return res;
    }

    ChainQueryResult *cycleResult(ChainSearchTreeNode *node)
    {
      CALL("AcyclicityIndex::ChainSearchIterator::cycleResult");

      ASS(node);
      ASS(node->parent);
      ASS(node->isUnificationNode);

      LiteralList* l = LiteralList::empty();
      ClauseList* c = ClauseList::empty();
      ClauseList* cTheta = ClauseList::empty();

      ChainSearchTreeNode *n = node;
      while (n && n->parent) {
        ASS(n);
        ASS(n->isUnificationNode);
        ASS(n->parent->clause);
        ASS(n->parent->clause->store() == Clause::ACTIVE);
        // TODO test order after subst
        LiteralList::push(n->parent->lit, l);
        ClauseList::push(n->parent->clause, c);
        ClauseList::push(applySubstitution(n->parent->clause, n->parent->substIndex), cTheta);
        n = n->parent->parent;
      }
      ASS_EQ(ClauseList::length(c), LiteralList::length(l));
      ASS_EQ(ClauseList::length(c), ClauseList::length(cTheta));

      return new ChainQueryResult(l, c, cTheta, nullptr);
    }

    ChainQueryResult *openChainResult(ChainSearchTreeNode *node, TermList t1, TermList tn, unsigned tnsort)
    {
      CALL("AcyclicityIndex::ChainSearchIterator::openChainResult");

      ASS(node);
      ASS(!node->isUnificationNode);

      ChainSearchTreeNode *n = node;
      LiteralList* l = LiteralList::empty();
      ClauseList* c = ClauseList::empty();
      ClauseList* cTheta = ClauseList::empty();
      LiteralList::push(n->lit, l);
      ClauseList::push(n->clause, c);
      ClauseList::push(applySubstitution(n->clause, n->substIndex), cTheta);
      n = n->parent;
      
      while (n && n->parent) {
        ASS(n);
        ASS(n->isUnificationNode);
        ASS(n->parent->clause);
        ASS(n->parent->clause->store() == Clause::ACTIVE);
        // TODO test order after subst
        LiteralList::push(n->parent->lit, l);
        ClauseList::push(n->parent->clause, c);
        ClauseList::push(applySubstitution(n->parent->clause, n->parent->substIndex), cTheta);
        n = n->parent->parent;
      }     
      ASS_EQ(ClauseList::length(c), LiteralList::length(l));
      ASS_EQ(ClauseList::length(c), ClauseList::length(cTheta));

      // TODO change predicate when axioms are changed
      Literal *subLit = nullptr;
      if (_querySort != tnsort || !TermList::equals(t1, tn)) {
        TermAlgebra* ta1 = env.signature->getTermAlgebraOfSort(_querySort);
        TermAlgebra* tan = env.signature->getTermAlgebraOfSort(tnsort);
        unsigned pred = ta1->getSubtermPredicate(tan);
        subLit = Literal::create2(pred,
                                  true,
                                  tn,
                                  t1);
      }
      return new ChainQueryResult(l, c, cTheta, subLit);
    }

    void pushUnificationsOnStack(ChainSearchTreeNode *n)
    {
      CALL("Acyclicity::pushUnificationOnStack");
      ASS(!n->isUnificationNode);

      TermQueryResultIterator tqrIt = _aindex._tis->getUnifications(_subst->apply(n->term, n->substIndex));
      unsigned sort = SortHelper::getTermSort(n->term, n->lit);
      int index;
      while (tqrIt.hasNext()) {
        TermQueryResult tqr = tqrIt.next();
        if (n->term.isVar() && tqr.literal != _queryLit) {
          // found a variable-ended chain, no need to explore further
          continue;
        }
        // check sort to avoid unfication with variable of wrong type
        if (SortHelper::getTermSort(tqr.term, tqr.literal) == sort) {
          // avoid cycles in the search tree
          if (tqr.literal == _queryLit || notInAncestors(n, tqr.literal)) {
            if (tqr.literal == _queryLit) {
              index = 0;
            } else if (n && tqr.clause == n->clause) {
              index = n->substIndex;
            } else {
              index = _nextAvailableIndex++;
            }
            _stack.push(ChainSearchTreeNode::unificationNode(tqr.term,
                                                             tqr.literal,
                                                             tqr.clause,
                                                             n,
                                                             index));
          }
        }
      }
    }

    // check that the literal is not found in the path from the root
    // to the node (to avoid infinite cycles in the search)
    bool notInAncestors(ChainSearchTreeNode *node, Literal *l)
    {
      CALL("AcyclicityIndex::ChainSearchIterator::notInAncestors");

      ChainSearchTreeNode *n = node;
      while (n) {
        if (n->lit == l) {
          return false;
        }
        n = n->parent;
      }

      return true;
    }

    bool hasNext()
    {
      CALL("AcyclicityIndex::ChainSearchIterator::hasNext");

      // if hasNext() has already been called without being followed
      // by a call to next(), the next value is already computed
      if (_nextResult) { return true; }

      while (_stack.isNonEmpty()) {
        ChainSearchTreeNode *n = _stack.pop();

        while (_currentDepth > n->depth) {
          _substChanges.pop().backtrack();
          _currentDepth--;
          ASS_EQ(_currentDepth, _substChanges.size());
        }

        if (n->isUnificationNode) {
          if (n->parent) {
            BacktrackData btData;
            _subst->bdRecord(btData);
            if (_subst->unify(n->parent->term,
                              n->parent->substIndex,
                              n->term,
                              n->substIndex)) {
              _substChanges.push(btData);
              _currentDepth++;
              ASS_EQ(_currentDepth, _substChanges.size());
              _subst->bdDone();
            } else {
              _subst->bdDone();
              ASS(btData.isEmpty());
              // unification can fail because the term indexing
              // structure can return "false positives", i.e. terms
              // that cannot unify (because they come from the same
              // clause)
              continue;
            }
          }
          if (n->parent) { // not the root of the search tree
            TermList t1 = _subst->apply(_queryTerm, 0);
            TermList tn = _subst->apply(n->term, n->substIndex);
            if (n->lit == _queryLit && TermList::equals(t1, tn)) {
              // found a cycle
              delete _nextResult;
              _nextResult = cycleResult(n);
              return true;
            }
          }
          if (_aindex._lIndex.find(make_pair(n->lit, n->clause))) {
            IndexEntry *entry = _aindex._lIndex.get(make_pair(n->lit, n->clause));
            List<TermList>::Iterator it(entry->subterms);
            while (it.hasNext()) {
              TermList t = it.next();
              _stack.push(ChainSearchTreeNode::subtermNode(t,
                                                           entry->lit,
                                                           entry->clause,
                                                           n,
                                                           n->substIndex));
            }
          }
        } else {
          if (n->term.isVar()) {
            // if the subterm is a variable, either we can close the
            // chain or have to return a variable-ended chain
            bool closed = false;
            if (SortHelper::getTermSort(n->term, n->lit) == _querySort) {
              BacktrackData btData;
              _subst->bdRecord(btData);
              closed = _subst->unify(_queryTerm, 0, n->term, n->substIndex);
              if (closed) {
                btData.backtrack();
              }
              _subst->bdDone();
              ASS(btData.isEmpty());
            }
            if (!closed) {
              delete _nextResult;
              TermList t1 = _subst->apply(_queryTerm, 0);
              TermList tn = _subst->apply(n->term, n->substIndex);
              _nextResult = openChainResult(n,
                                            t1,
                                            tn,
                                            SortHelper::getTermSort(n->term, n->lit));
              return true;
            }
          }
          // either not a variable or a variable closing the chain
          // look for unifications
          // if a variable, this will only push the unification with
          // the queryTerm
          pushUnificationsOnStack(n);
        }
      }
      return false;
    }
    
    ChainQueryResult next()
    {
      CALL("AcyclicityIndex::ChainSearchIterator::next()");

      ASS(_nextResult);
      ChainQueryResult *res = _nextResult;
      _nextResult = nullptr;
      return *res;
    }
  private:
    Literal *_queryLit;
    Clause *_queryClause;
    TermList _queryTerm;
    unsigned _querySort;
    AcyclicityIndex &_aindex;
    ChainQueryResult *_nextResult;
    Stack<ChainSearchTreeNode*> _stack;
    RobSubstitution *_subst;
    Stack<BacktrackData> _substChanges;
    int _nextAvailableIndex;
    unsigned _currentDepth;
  };

  void AcyclicityIndex::handleClause(Clause* c, bool adding)
  {
    CALL("AcyclicityIndex::handleClause");

    // TODO timer?
    
    ArrayishObjectIterator<Clause> it = c->getSelectedLiteralIterator();
    while (it.hasNext()) {
      if (adding) {
        insert(it.next(), c);
      } else {
        remove(it.next(), c);
      }
    }
  }
    
  void AcyclicityIndex::insert(Literal *lit, Clause *c)
  {
    CALL("AcyclicityIndex::insert");

    TermList *fs;
    TermList *t;
    unsigned sort;
    
    if (matchesPattern(lit, fs, t, &sort)) {
      ASS(fs->isTerm());

      ULit ulit = make_pair(lit, c);
      if (!_lIndex.find(ulit)) {
        _lIndex.insert(ulit, new IndexEntry(lit, c, *t, getSubterms(fs->term())));
        _tis->insert(*t, lit, c);
      }
    }
  }

  void AcyclicityIndex::remove(Literal *lit, Clause *c)
  {
    CALL("AcyclicityIndex::remove");

    TermList *fs;
    TermList *t;
    unsigned sort;
     
    if (matchesPattern(lit, fs, t, &sort)) {
      ULit ulit = make_pair(lit, c);
      if (!_lIndex.find(ulit))
        return;

      _lIndex.remove(ulit);
     _tis->remove(*t, lit, c);
    }
  }

  VirtualIterator<ChainQueryResult> AcyclicityIndex::queryChains(Literal *lit, Clause *c)
  {
    CALL("AcyclicityIndex::queryCycle");

    return vi(new ChainSearchIterator(lit, c, *this));
  }

  bool TARulesRHSIndex::rhsEligible(Literal* lit, const Ordering& ord, TermList*& lhs, TermList*& rhs)
  {
    CALL("TARulesRHSIndex::rhsEligible");

    if (lit->isEquality()
        && lit->isPositive()
        && env.signature->isTermAlgebraSort(SortHelper::getEqualityArgumentSort(lit))) {

      TermList *s = lit->nthArgument(0);
      TermList *t = lit->nthArgument(1);
      bool cons0 =  s->isTerm() && env.signature->getFunction(s->term()->functor())->termAlgebraCons();
      bool cons1 =  t->isTerm() && env.signature->getFunction(t->term()->functor())->termAlgebraCons();

      if (cons0) {
        if (cons1) {
          // literals of the form f(...) = g(...) should already have
          // been simplified, no need to consider them
          return false;
        }
        lhs = lit->nthArgument(0);
        rhs = lit->nthArgument(1);
        Ordering::Result o = ord.getEqualityArgumentOrder(lit);
        return (o == Ordering::INCOMPARABLE || o == Ordering::GREATER || o == Ordering::GREATER_EQ);
      } else if (cons1) {
        lhs = lit->nthArgument(1);
        rhs = lit->nthArgument(0);
        Ordering::Result o = ord.getEqualityArgumentOrder(lit);
        return (o == Ordering::INCOMPARABLE || o == Ordering::LESS || o == Ordering::LESS_EQ);
      }
    }
    return false;
  }

  void TARulesRHSIndex::handleClause(Clause* c, bool adding)
  {
    CALL("TARulesRHSIndex::handleClause");

    // TODO timer?

    unsigned selCnt=c->numSelected();
    TermList *lhs, *rhs;
    for (unsigned i=0; i<selCnt; i++) {
      Literal* lit=(*c)[i];
      if (rhsEligible(lit, _ord, lhs, rhs)) {
        if (adding) {
          _is->insert(*rhs, lit, c);
        } else {
          _is->remove(*rhs, lit, c);
        }
      }        
    }
  }
}
