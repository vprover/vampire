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
 * @file AcyclicityIndex.cpp
 * Implements class AcyclicityIndex
 */

#include "Kernel/Inference.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/TypedTermList.hpp"

#include "Lib/Backtrackable.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Stack.hpp"

#include "AcyclicityIndex.hpp"

using namespace std;
using namespace Kernel;
using namespace Lib;

namespace Indexing
{
  unsigned CycleQueryResult::totalLengthClauses()
  {
    unsigned n = 0;
    List<Clause*>::Iterator it(premises);
    while (it.hasNext()) {
      n += it.next()->length();
    }

    return n;
  }

  void addSubterm(TypedTermList t, List<TypedTermList>*& l)
  {
    List<TypedTermList>::Iterator it(l);
    while (it.hasNext()) {
      // TODO test for unifiability, keep only most general term
      if (TermList::equals(t, it.next())) {
        return;
      }
    }
    List<TypedTermList>::push(t, l);
  }
  
  List<TypedTermList>* AcyclicityIndex::getSubterms(Term *t)
  {
    Stack<Term*> toVisit;
    List<TypedTermList>* res = List<TypedTermList>::empty();
    
    TermList sort = SortHelper::getResultSort(t);
    ASS(env.signature->isTermAlgebraSort(sort));

    for (unsigned i = 0; i < t->arity(); i++) {
      if (SortHelper::getArgSort(t, i) == sort) {
        TermList *s = t->nthArgument(i);
        addSubterm(TypedTermList(*s,sort), res);
        if (s->isTerm()) {
          toVisit.push(s->term());
        }
      }
    }

    while (toVisit.isNonEmpty()) {
      Term *u = toVisit.pop();
      if (env.signature->getFunction(u->functor())->termAlgebraCons()) {
        for (unsigned i = 0; i < u->arity(); i++) {
          if (SortHelper::getArgSort(u, i) == sort) {
            TermList *s = u->nthArgument(i);
            addSubterm(TypedTermList(*s,sort), res);
            if (s->isTerm()) {
              toVisit.push(s->term());
            }
          }
        }
      }
    }
    
    return res;
  }

  bool AcyclicityIndex::matchesPattern(Literal *lit, TermList *&fs, TermList *&t, TermList *sort)
  {
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
    } else if (termAlgebraConsL && !termAlgebraConsR) {
      fs = l;
      t = r;
    } else {
      return false;
    }

    return true;
  }
  
  struct AcyclicityIndex::IndexEntry {
  public:
    IndexEntry(Literal *l, Clause *c, TypedTermList t, List<TypedTermList>* subterms) :
      lit(l),
      clause(c),
      t(t),
      subterms(subterms)
    {}

    USE_ALLOCATOR(AcyclicityIndex::IndexEntry);

    Literal* lit;
    Clause* clause;
    TypedTermList t;
    List<TypedTermList>* subterms;
  };

  struct AcyclicityIndex::CycleSearchTreeNode
  {
    CycleSearchTreeNode(TypedTermList t,
                        Literal *l,
                        Clause *c,
                        CycleSearchTreeNode *n,
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

    static CycleSearchTreeNode *subtermNode(TypedTermList t,
                                     Literal *l,
                                     Clause *c,
                                     CycleSearchTreeNode *n,
                                     unsigned substIndex)
    {
      return new CycleSearchTreeNode(t, l, c, n, n ? n->depth + 1 : 0, substIndex, false);
    }

    static CycleSearchTreeNode *unificationNode(TypedTermList t,
                                         Literal *l,
                                         Clause *c,
                                         CycleSearchTreeNode *n,
                                         unsigned substIndex)
    {
      return new CycleSearchTreeNode(t, l, c, n, n ? n->depth : 0, substIndex, true);
    }

    USE_ALLOCATOR(AcyclicityIndex::CycleSearchTreeNode);

    TypedTermList term;
    Literal *lit;
    Clause *clause;
    CycleSearchTreeNode *parent;
    unsigned depth;
    unsigned substIndex;
    bool isUnificationNode;

  };

  struct AcyclicityIndex::CycleSearchIterator
  {
    CycleSearchIterator(Literal *queryLit,
                        Clause *queryClause,
                        AcyclicityIndex& aindex)
      :
      _queryLit(queryLit),
      _index(nullptr),
      _tis(nullptr),
      _nextResult(nullptr),
      _stack(0),
      _subst(new RobSubstitution()),
      _substChanges(0),
      _nextAvailableIndex(0),
      _currentDepth(0)
    {
      if (queryLit->isEquality()) {
        TermList sort = SortHelper::getEqualityArgumentSort(queryLit);

        if (aindex._sIndexes.find(sort)) {
          _index = aindex._sIndexes.get(sort);
          _tis = aindex._tis;
          if (_index->find(make_pair(queryLit, queryClause))) {
            IndexEntry *entry = _index->get(make_pair(queryLit, queryClause));
            _stack.push(CycleSearchTreeNode::unificationNode(entry->t,
                                                             queryLit,
                                                             queryClause,
                                                             nullptr,
                                                             _nextAvailableIndex++));
          }
        }
      }
      ASS_EQ(_currentDepth, _substChanges.size());
    }
    
    DECL_ELEMENT_TYPE(CycleQueryResult*);

    Clause *applySubstitution(Clause *c, unsigned index)
    {
      RStack<Literal*> resLits;

      for (auto lit : c->iterLits()) {
        resLits->push(_subst->apply(lit, index));
      }

      return Clause::fromStack(*resLits,
          GeneratingInference1(InferenceRule::INSTANTIATION, c));
    }

    CycleQueryResult *resultFromNode(CycleSearchTreeNode *node)
    {
      LiteralList* l = LiteralList::empty();
      ClauseList* c = ClauseList::empty();
      ClauseList* cTheta = ClauseList::empty();

      CycleSearchTreeNode *n = node;
      while (n && n->parent) {
        ASS(n);
        ASS(n->isUnificationNode);
        ASS(n->parent->clause);
        ASS(n->parent->clause->store() == Clause::ACTIVE);
        Clause *cl = applySubstitution(n->parent->clause, n->parent->substIndex);
        LiteralList::push(n->parent->lit, l);
        ClauseList::push(n->parent->clause, c);
        ClauseList::push(cl, cTheta);
        n = n->parent->parent;
      }

      ASS_EQ(ClauseList::length(c), LiteralList::length(l));
      ASS_EQ(ClauseList::length(c), ClauseList::length(cTheta));

      return new CycleQueryResult(l, c, cTheta);
    }

    void pushUnificationsOnStack(TypedTermList t, CycleSearchTreeNode *parent)
    {
      // ASS(t.isTerm());
      ASS(_tis);
      auto tqrIt = _tis->getUnifications(t);
      int index;
      while (tqrIt.hasNext()) {
        auto tqr = tqrIt.next();
        if (tqr.data->literal == _queryLit || notInAncestors(parent, tqr.data->literal)) {
          if (tqr.data->literal == _queryLit) {
            index = 0;
          } else if (parent && tqr.data->clause == parent->clause) {
            index = parent->substIndex;
          } else {
            index = _nextAvailableIndex++;
          }
          _stack.push(CycleSearchTreeNode::unificationNode(tqr.data->term,
                                                           tqr.data->literal,
                                                           tqr.data->clause,
                                                           parent,
                                                           index));
        }
      }
    }

    bool notInAncestors(CycleSearchTreeNode *node, Literal *l)
    {
      CycleSearchTreeNode *n = node;
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
      // if hasNext() has already been called without being followed
      // by a call to next(), the next value is already computed
      if (_nextResult) { return true; }

      while (_stack.isNonEmpty()) {
        CycleSearchTreeNode *n = _stack.pop();

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
          if (n->lit == _queryLit && n->parent) {
            _nextResult = resultFromNode(n);
            return true;
          }
          if (_index->find(make_pair(n->lit, n->clause))) {
            IndexEntry *entry = _index->get(make_pair(n->lit, n->clause));
            List<TypedTermList>::Iterator it(entry->subterms);
            while (it.hasNext()) {
              TypedTermList t = it.next();
              _stack.push(CycleSearchTreeNode::subtermNode(t,
                                                           entry->lit,
                                                           entry->clause,
                                                           n,
                                                           n->substIndex));
            }
          }
        } else {
          pushUnificationsOnStack(TypedTermList(_subst->apply(n->term, n->substIndex),_subst->apply(n->term.sort(), n->substIndex)), n);
        }
      }
      return false;
    }
    
    OWN_ELEMENT_TYPE next()
    {
      ASS(_nextResult);
      CycleQueryResult *res = _nextResult;
      _nextResult = nullptr;
      return res;
    }
  private:
    Literal *_queryLit;
    SIndex *_index;
    TermIndexingStructure *_tis;
    CycleQueryResult *_nextResult;
    Stack<CycleSearchTreeNode*> _stack;
    RobSubstitution *_subst;
    Stack<BacktrackData> _substChanges;
    int _nextAvailableIndex;
    unsigned _currentDepth;
  };

  void AcyclicityIndex::handleClause(Clause* c, bool adding)
  {
    auto it = c->getSelectedLiteralIterator();
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
    TermList *fs;
    TermList *t;
    TermList sort;
    
    if (matchesPattern(lit, fs, t, &sort)) {
      ASS(fs->isTerm());

      SIndex* index;
      if (_sIndexes.find(sort)) {
        index = _sIndexes.get(sort);
      } else {
        // initialize the index for this sort
        index = new SIndex();
        _sIndexes.insert(sort, index);
      }

      ULit ulit = make_pair(lit, c);
      if (!index->find(ulit)) {
        index->insert(ulit, new IndexEntry(lit, c, TypedTermList(*t,sort), getSubterms(fs->term())));
        _tis->insert(TermLiteralClause{ TypedTermList(*t, sort), lit, c });
      }
    }
  }

  void AcyclicityIndex::remove(Literal *lit, Clause *c)
  {
    TermList *fs;
    TermList *t;
    TermList sort;
     
    if (matchesPattern(lit, fs, t, &sort) && _sIndexes.find(sort)) {
      ULit ulit = make_pair(lit, c);
      if (!_sIndexes.get(sort)->find(ulit))
        return;

      _sIndexes.get(sort)->remove(ulit);
      _tis->remove(TermLiteralClause{ TypedTermList(*t, sort), lit, c });
    }
  }

  CycleQueryResultsIterator AcyclicityIndex::queryCycles(Literal *lit, Clause *c)
  {
    return pvi(CycleSearchIterator(lit, c, *this));
  }
}
