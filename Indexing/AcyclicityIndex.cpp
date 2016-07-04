/**
 * @file AcyclicityIndex.cpp
 * Implements class AcyclicityIndex
 */

#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"

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

    // TODO remove the groundness test on t
    return (t->isTerm() && t->term()->ground() && !Ordering::isGorGEorE(_ord.compare(*t, *fs)));
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
    CycleSearchTreeNode(TermList *t, Literal *l, Clause *c, CycleSearchTreeNode *n)
      :
      term(t),
      lit(l),
      clause(c),
      parent(n),
      subst()
    {}

    CycleSearchTreeNode(Literal *l, ResultSubstitutionSP subst, CycleSearchTreeNode *n)
      :
      term(nullptr),
      lit(l),
      clause(nullptr),
      parent(n),
      subst(subst)
    {}

    TermList *term;
    Literal *lit;
    Clause *clause;
    CycleSearchTreeNode *parent;
    ResultSubstitutionSP subst;

    bool isInstance() {
      return !subst.isEmpty();
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
      _stack(0)
    {
      if (queryLit->isEquality()) {
        unsigned sort = SortHelper::getEqualityArgumentSort(queryLit);

        if (aindex._sIndexes.find(sort)) {
          _index = aindex._sIndexes.get(sort);
          _tis = aindex._tis;
          if (_index->find(queryLit)) {
            IndexEntry *entry = _index->get(queryLit);
            List<TermList*>::Iterator it(entry->subterms);
            while (it.hasNext()) {
              pushUnificationsOnStack(*it.next(), nullptr);
            }
          }
        }
      }
    }
    
    DECL_ELEMENT_TYPE(CycleQueryResult*);

    CycleQueryResult *resultFromNode(CycleSearchTreeNode *node)
    {
      CALL("AcyclicityIndex::CycleSearchIterator::resultFromNode");

      List<Literal*>* l = List<Literal*>::empty();
      List<Clause*>* c = List<Clause*>::empty();
      List<Clause*>* cTheta = List<Clause*>::empty();

      CycleSearchTreeNode *n = node;
      while (n) {
        ASS(n);
        ASS(!n->isInstance());
        ASS(n->parent);
        cTheta = cTheta->cons(n->clause);
        l = l->cons(n->lit);
        c = c->cons(n->clause);
        n = n->parent->parent;
      }

      ASS_EQ(l->length(), c->length());
      ASS_EQ(l->length(), cTheta->length());

      return new CycleQueryResult(l, c, cTheta);
    }

    void pushUnificationsOnStack(TermList t, CycleSearchTreeNode *parent)
    {
      CALL("Acyclicity::pushUnificationOnStack");

      TermQueryResultIterator tqrIt = _tis->getUnifications(t);
      while (tqrIt.hasNext()) {
        TermQueryResult tqr = tqrIt.next();
        if (notInAncestors(parent, tqr.literal)) {
          // TODO could add an ordering test after substitution
          _stack.push(new CycleSearchTreeNode(tqr.literal,
                                              tqr.substitution,
                                              parent));
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

      if (_nextResult) { return true; }

      while (_stack.isNonEmpty()) {
        CycleSearchTreeNode *n = _stack.pop();

        if (n->isInstance()) {
          if (_index->find(n->lit)) {
            IndexEntry *entry = _index->get(n->lit);
            List<TermList*>::Iterator it(entry->subterms);
            while (it.hasNext()) { 
              _stack.push(new CycleSearchTreeNode(it.next(), entry->lit, entry->clause, n));
            }
          }
        } else if (n->lit == _queryLit) {
          _nextResult = resultFromNode(n);
          return true;
        } else {
          pushUnificationsOnStack(n->parent->subst->applyToResult(*n->term), n->parent);
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

      if (index->find(lit)) {
        return;
      }
      
      _tis->insert(*t, lit, c);
      index->insert(lit, new IndexEntry(lit, c, t, getSubterms(fs->term())));
    }
  }

  void AcyclicityIndex::remove(Literal *lit, Clause *c)
  {
    CALL("AcyclicityIndex::remove");

    TermList *fs;
    TermList *t;
    unsigned sort;
     
    if (matchesPattern(lit, fs, t, &sort) && _sIndexes.find(sort)) {
      ASS(_sIndexes.get(sort)->find(lit));
      _sIndexes.get(sort)->remove(lit);
      _tis->remove(*t, lit, c);
    }
  }

  CycleQueryResultsIterator AcyclicityIndex::queryCycles(Literal *lit, Clause *c)
  {
    CALL("AcyclicityIndex::queryCycle");

    return pvi(CycleSearchIterator(lit, c, *this));
  }
}
