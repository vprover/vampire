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

#include "AcyclicityIndex.hpp"

using namespace Kernel;
using namespace Lib;

namespace Indexing
{
  unsigned CycleQueryResult::totalLengthClauses()
  {
    CALL("CycleQueryResult::totalLengthClauses");

    unsigned n = 0;
    List<Clause*>::Iterator it(premises);
    while (it.hasNext()) {
      n += it.next()->length();
    }

    return n;
  }
  
  List<TermList*>* AcyclicityIndex::getSubterms(Term *t)
  {
    CALL("AcyclicityIndex::getSubterms");
    
    Stack<Term*> toVisit;
    List<TermList*>* res = List<TermList*>::empty();
    
    unsigned sort = SortHelper::getResultSort(t);
    ASS(env.signature->isTermAlgebraSort(sort));

    for (unsigned i = 0; i < t->arity(); i++) {
      if (SortHelper::getArgSort(t, i) == sort) {
        TermList *s = t->nthArgument(i);
        res = res->cons(s);
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
            res = res->cons(s);
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
    } else if (termAlgebraConsL && !termAlgebraConsR) {
      fs = l;
      t = r;
    } else {
      return false;
    }

    return (!Ordering::isGorGEorE(_ord.compare(*t, *fs)));
  }
  
  struct AcyclicityIndex::IndexEntry {
  public:
    IndexEntry(Literal *l, Clause *c, TermList *t, List<TermList*>* subterms) :
      lit(l),
      clause(c),
      t(t),
      subterms(subterms)
    {}

    Literal* lit;
    Clause* clause;
    TermList* t;
    List<TermList*>* subterms;
  };

  struct AcyclicityIndex::CycleSearchTreeNode
  {
    CycleSearchTreeNode(TermList *t, Literal *l, Clause *c, CycleSearchTreeNode *n, int substIndex)
      :
      term(t),
      lit(l),
      clause(c),
      parent(n),
      depth(n->parent ? n->depth + 1 : 0),
      substIndex(substIndex)
    {}

    CycleSearchTreeNode(TermList *t, Literal *l, CycleSearchTreeNode *n, int substIndex)
      :
      term(t),
      lit(l),
      clause(nullptr),
      parent(n),
      depth(n ? n->depth : 0),
      substIndex(substIndex)
    {}

    TermList *term;
    Literal *lit;
    Clause *clause;
    unsigned substIndex;
    CycleSearchTreeNode *parent;
    unsigned depth;

    bool isUnificationNode() {
      return (!clause);
    }
  };

  struct AcyclicityIndex::CycleSearchIterator
  {
    CycleSearchIterator(Literal *queryLit,
                        Clause *queryClause,
                        AcyclicityIndex& aindex)
      :
      _queryLit(queryLit),
      _queryClause(queryClause),
      _nextResult(nullptr),
      _stack(0),
      _subst(new RobSubstitution()),
      _substChanges(0),
      _nextAvailableIndex(0),
      _currentDepth(0)
    {
      CALL("AcyclicityIndex::CycleSearchIterator");
      
      if (queryLit->isEquality()) {
        unsigned sort = SortHelper::getEqualityArgumentSort(queryLit);

        if (aindex._sIndexes.find(sort)) {
          _index = aindex._sIndexes.get(sort);
          _tis = aindex._tis;
          if (_index->find(queryLit)) {
            IndexEntry *entry = _index->get(queryLit);
            //cout << "--------------------------------" << endl;
            //cout << "push first node " << *entry->t << "/" << _nextAvailableIndex << endl;
            //cout << _subst->toString() << endl;
            _stack.push(new CycleSearchTreeNode(entry->t,
                                                queryLit,
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
      CALL("AcyclicityIndex::applySubstitution");
      
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

    CycleQueryResult *resultFromNode(CycleSearchTreeNode *node)
    {
      CALL("AcyclicityIndex::CycleSearchIterator::resultFromNode");

      List<Literal*>* l = List<Literal*>::empty();
      List<Clause*>* c = List<Clause*>::empty();
      List<Clause*>* cTheta = List<Clause*>::empty();

      //cout << "new clause with subst=" << _subst->toString() << endl;

      CycleSearchTreeNode *n = node;
      while (n && n->parent) {
        ASS(n);
        ASS(n->isUnificationNode());
        ASS(n->parent->clause);
        ASS(n->parent->clause->store() == Clause::ACTIVE);
        Clause *cl = applySubstitution(n->parent->clause, n->parent->substIndex);
        cTheta = cTheta->cons(cl);
        l = l->cons(n->parent->lit);
        c = c->cons(n->parent->clause);
        n = n->parent->parent;
      }

      ASS_EQ(l->length(), c->length());
      ASS_EQ(l->length(), cTheta->length());

      return new CycleQueryResult(l, c, cTheta);
    }

    void pushUnificationsOnStack(TermList t, CycleSearchTreeNode *parent)
    {
      CALL("Acyclicity::pushUnificationOnStack");

      //cout << "querying unifications for " << t << endl;

      ASS(_tis);
      TermQueryResultIterator tqrIt = _tis->getUnifications(t);
      int index;
      while (tqrIt.hasNext()) {
        TermQueryResult tqr = tqrIt.next();
        if (tqr.literal == _queryLit || notInAncestors(parent, tqr.literal)) {
          if (tqr.literal == _queryLit) {
            index = 0;
          } else if (parent && tqr.clause == parent->clause) {
            index = parent->substIndex;
          } else {
            index = _nextAvailableIndex++;
          }
          //cout << "push unification node " << tqr.term << "/" << index << endl;
          _stack.push(new CycleSearchTreeNode(new TermList(tqr.term),
                                              tqr.literal,
                                              parent,
                                              index));
        }
      }
    }

    bool notInAncestors(CycleSearchTreeNode *node, Literal *l)
    {
      CALL("AcyclicityIndex::CycleSearchIterator::notInAncestors");

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
      CALL("AcyclicityIndex::CycleSearchIterator::hasNext");

      // if hasNext() has already been called without being followed
      // by a call to next(), the next value is already computed
      if (_nextResult) { return true; }

      while (_stack.isNonEmpty()) {
        CycleSearchTreeNode *n = _stack.pop();

        while (_currentDepth > n->depth) {
          BacktrackData *btData = _substChanges.pop();
          //cout << "popping data " << btData << endl;
          btData->backtrack();
          btData->~BacktrackData();
          _currentDepth--;
          ASS_EQ(_currentDepth, _substChanges.size());
          //cout << "> backtracking to " << _currentDepth << endl;
          //cout << _subst->toString() << endl;
        }

        if (n->isUnificationNode()) {
          //cout << "pop unification node " << *n->term << "/" << n->substIndex << endl;
          if (n->parent) {
            BacktrackData *btData = new BacktrackData();
            _subst->bdRecord(*btData);
            /*cout << "try unification " << *n->parent->term
                 << "/" << n->parent->substIndex
                 << " and " << *n->term
                 << "/" << n->substIndex << endl;*/
            if (_subst->unify(*n->parent->term,
                              n->parent->substIndex,
                              *n->term,
                              n->substIndex)) {
              // TODO add ordering test
              //cout << "pushing data " << btData << endl;
              _substChanges.push(btData);
              _currentDepth++;
              ASS_EQ(_currentDepth, _substChanges.size());
              //cout << "> unifying to " << _currentDepth << endl;
              //cout << _subst->toString() << endl;
              _subst->bdDone();
            } else {
              _subst->bdDone();
              ASS(btData->isEmpty());
              btData->~BacktrackData();
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
          if (_index->find(n->lit)) {
            IndexEntry *entry = _index->get(n->lit);
            List<TermList*>::Iterator it(entry->subterms);
            while (it.hasNext()) {
              TermList *t = it.next();
              //cout << "push subterm node " << *t << "/" << n->substIndex << endl;
              _stack.push(new CycleSearchTreeNode(t,
                                                  entry->lit,
                                                  entry->clause,
                                                  n,
                                                  n->substIndex));
            }
          }
        } else {
          //cout << "pop subterm node " << *n->term << "/" << n->substIndex << endl;
          pushUnificationsOnStack(_subst->apply(*n->term, n->substIndex), n);
        }
      }
      return false;
    }
    
    OWN_ELEMENT_TYPE next()
    {
      CALL("AcyclicityIndex::CycleSearchIterator::next()");

      ASS(_nextResult);
      CycleQueryResult *res = _nextResult;
      _nextResult = nullptr;
      return res;
    }
  private:
    Literal *_queryLit;
    Clause *_queryClause;
    SIndex *_index;
    TermIndexingStructure *_tis;    
    CycleQueryResult *_nextResult;
    Stack<CycleSearchTreeNode*> _stack;
    RobSubstitution *_subst;
    Stack<BacktrackData*> _substChanges;
    int _nextAvailableIndex;
    unsigned _currentDepth;
  };

  void AcyclicityIndex::handleClause(Clause* c, bool adding)
  {
    CALL("AcyclicityIndex::handleClause");

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

      SIndex* index;
      if (_sIndexes.find(sort)) {
        index = _sIndexes.get(sort);
      } else {
        // initialize the index for this sort
        index = new SIndex();
        _sIndexes.insert(sort, index);
      }

      if (!index->find(lit)) {
        index->insert(lit, new IndexEntry(lit, c, t, getSubterms(fs->term())));
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
     
    if (matchesPattern(lit, fs, t, &sort) && _sIndexes.find(sort) && _sIndexes.get(sort)->find(lit)) {
      _sIndexes.get(sort)->remove(lit);

      // in some rare cases, this call leads to a segfault in the
      // substitution tree, even though the entry (t, lit, c) should be
      // present.
      // TODO find cause and reactivate the removal
      
      //_tis->remove(*t, lit, c);
    }
  }

  CycleQueryResultsIterator AcyclicityIndex::queryCycles(Literal *lit, Clause *c)
  {
    CALL("AcyclicityIndex::queryCycle");

    return pvi(CycleSearchIterator(lit, c, *this));
  }
}
