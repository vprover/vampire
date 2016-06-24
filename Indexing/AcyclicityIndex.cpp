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
  struct AcyclicityIndex::SubtermIterator {
    SubtermIterator(Term *t)
    {
      Stack<Term*> toVisit;
      unsigned sort = SortHelper::getResultSort(t);
      ASS(env.signature->isTermAlgebraSort(sort));

      for (unsigned i = 0; i < t->arity(); i++) {
        if (SortHelper::getArgSort(t, i) == sort) {
          TermList *s = t->nthArgument(i);
          _subterms.push(s);
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
              _subterms.push(s);
              if (s->isTerm()) {
                toVisit.push(s->term());
              }
            }
          }
        }
      }
    }

    DECL_ELEMENT_TYPE(TermList*);
    
    bool hasNext()
    {
      CALL("AcyclicityIndex::SubtermIterator::hasNext");

      return _subterms.isNonEmpty();
    }

    OWN_ELEMENT_TYPE next()
    {
      CALL("AcyclicityIndex::SubtermIterator::hasNext");

      return _subterms.pop();
    }

    Stack<TermList*> _subterms;
  };
    
  struct AcyclicityIndex::IndexEntry {
  public:
    IndexEntry(Literal *l, Clause *c, TermList *t) :
      _lit(l),
      _clause(c),
      _term(t)
    {}
    
  protected:
    Literal* _lit;
    Clause* _clause;
    TermList* _term;
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
        
    if (!lit->isEquality() || !lit->polarity()) {
      return;
    }

    unsigned sort = SortHelper::getEqualityArgumentSort(lit);
    if (!env.signature->isTermAlgebraSort(sort)) {
      return;
    }

    TermList *l = lit->nthArgument(0);
    TermList *r = lit->nthArgument(1);
    
    bool termAlgebraConsL = l->isTerm() && env.signature->getFunction(l->term()->functor())->termAlgebraCons();
    bool termAlgebraConsR = r->isTerm() && env.signature->getFunction(r->term()->functor())->termAlgebraCons();
    
    if (!termAlgebraConsL && termAlgebraConsR) {
      TermList *swap = l; l = r; r = swap;
    } else if (!termAlgebraConsL || termAlgebraConsR) {
      return;
    }

    ASS(l->isTerm());

    if (!Ordering::isGorGEorE(_ord.compare(*r, *l))) {
      SIndex* index;
      if (_sIndexes.find(sort)) {
        index = _sIndexes.get(sort);
      } else {
        // initialize the index for this sort
        index = new SIndex();
        _sIndexes.insert(sort, index);
      }

      List<IndexEntry*>* list;
      if (index->find(r)) {
        list = index->get(r);
      } else {
        list = List<IndexEntry*>::empty();
      }
      
      SubtermIterator it(l->term());
      while (it.hasNext()) {
        IndexEntry *entry = new IndexEntry(lit, c, it.next());
        list = list->cons(entry);
      }
      index->insert(r, list);
    }
  }

  void AcyclicityIndex::remove(Literal *lit, Clause *c)
  {
    CALL("AcyclicityIndex::remove");

    //TODO
  }
}
