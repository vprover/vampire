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
 * @file TermAlgebraReasoning.cpp
 */

#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/SortHelper.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Stack.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "TermAlgebraReasoning.hpp"

#include <cstring>

using namespace Kernel;
using namespace Lib;

namespace Inferences {

  // copy clause c, replacing literal a by b
  Clause* replaceLit(Clause *c, Literal *a, Literal *b, const Inference& inf)
  {
    RStack<Literal*> resLits;
    for (auto lit : c->iterLits()) {
      resLits->push(lit == a ? b : lit);
    }
    return Clause::fromStack(*resLits,inf);
  }

  // copy clause c, with the exception of the i-th literal
  Clause* removeLit(Clause *c, unsigned i, const Inference& inf)
  {
    ASS_GE(i, 0);
    ASS_L(i, c->length());

    RStack<Literal*> resLits;
    for (auto j : range(0, c->size())) {
      if (j != i) {
        resLits->push((*c)[j]);
      }
    }

    return Clause::fromStack(*resLits,inf);
  }

  // return f is the term has the form f(x1 ... xn) and f is a term
  // algebra constructor, or nullptr otherwise
  Signature::Symbol* termAlgebraConstructor(TermList *t)
  {
    if (t->isTerm()) {
      Signature::Symbol *s = env.signature->getFunction(t->term()->functor());

      if (s->termAlgebraCons()) {
        return s;
      }
    }
    return nullptr;
  }

  // true iff the literal has the form f(x1 ... xn) =? g(y1 ... ym)
  // where f and g term algebra constructors. =? stands for either
  // equality of disequality
  bool distinctConstructorsEquality(Literal *lit)
  {
    if (!lit->isEquality())
      return false;

    Signature::Symbol *s = termAlgebraConstructor(lit->nthArgument(0));
    Signature::Symbol *t = termAlgebraConstructor(lit->nthArgument(1));

    return (s && t && s != t);
  }

  // true iff the literal has the form f(x1 ... xn) = f(y1 ... yn)
  // where f is a term algebra constructor
  bool sameConstructorsEquality(Literal *lit)
  {
    if (!lit->isEquality())
      return false;

    Signature::Symbol *s = termAlgebraConstructor(lit->nthArgument(0));
    Signature::Symbol *t = termAlgebraConstructor(lit->nthArgument(1));

    return (s && s == t);
  }

  Clause* DistinctnessISE::simplify(Clause* c)
  {
    if (c->isPureTheoryDescendant())
      return c;
    
    int length = c->length();
    for (int i = length - 1; i >= 0; i--) {
      Literal *lit = (*c)[i];
      if (distinctConstructorsEquality(lit)) {
        if (lit->isPositive()) {
          // equality of the form f(x) = g(y), delete literal from clause
          Clause* res = removeLit(c, i, SimplifyingInference1(InferenceRule::TERM_ALGEBRA_DISTINCTNESS, c));
          return res;
        } else {
          // inequality of the form f(x) != g(y) are theory tautologies
          env.statistics->taDistinctnessTautologyDeletions++;
          return 0;
        }
      }
    }

    // no equalities between distinct constructors were found
    return c;
  }

  /*
   * Given a clause f(x1, ..., xn) = f(y1, ... yn) \/ A, this iterator
   * returns the clauses x1 = y1 \/ A up to xn = yn \/ A. For any
   * other literal the iterator is empty
   */
  struct InjectivityGIE::SubtermIterator
  {
    SubtermIterator(Clause *clause, Literal *lit)
      : _index(0),
        _lit(lit),
        _clause(clause)
    {
      if (lit->polarity() && sameConstructorsEquality(lit)) {
        _index = lit->nthArgument(0)->term()->numTypeArguments();
        _length = lit->nthArgument(0)->term()->arity();
      } else {
        _length = 0;
      }
    }

    DECL_ELEMENT_TYPE(Clause *);

    bool hasNext() { return _index < _length; }
    OWN_ELEMENT_TYPE next()
    {
      // from the clause f(x1 ... xn) = f(y1 .. yn) \/ C, we create
      // a new clause xi = yi \/ C. In this case, next() can be
      // called n times to create the n relevant conclusions.
      Literal *l = Literal::createEquality(true,
                                           *_lit->nthArgument(0)->term()->nthArgument(_index),
                                           *_lit->nthArgument(1)->term()->nthArgument(_index),
                                           SortHelper::getArgSort(_lit->nthArgument(0)->term(), _index));
      
      Clause * res = replaceLit(_clause, _lit, l, GeneratingInference1(InferenceRule::TERM_ALGEBRA_INJECTIVITY_GENERATING, _clause));
      _index++;
      return res;
    }
  private:
    unsigned int _length; // this is the arity n of the constructor f
                          // if _lits is a positive equality between
                          // two identical constructors, 1 if _lits is
                          // a negative equality between two
                          // constructors, 0 in any other case
    unsigned int _index; // between 0 and _length
    Literal* _lit;
    Clause* _clause;
  };

  struct InjectivityGIE::SubtermEqualityFn
  {
    SubtermEqualityFn(Clause* premise)
      : _premise(premise) {}
    VirtualIterator<Clause*> operator()(Literal* lit)
    {
      return pvi(SubtermIterator(_premise, lit));
    }
  private:
    Clause* _premise;
  };

  ClauseIterator InjectivityGIE::generateClauses(Clause* c)
  {
    auto it1 = c->getSelectedLiteralIterator();
    auto it2 = getMappingIterator(it1, SubtermEqualityFn(c));
    auto it3 = getFlattenedIterator(it2);
    return pvi(it3);
  }

  Clause* InjectivityISE::simplify(Clause *c)
  {
    if (c->isPureTheoryDescendant())
      return c;

    int length = c->length();
    for (int i = length - 1; i >= 0; i--) {
      Literal *lit = (*c)[i];
      if (sameConstructorsEquality(lit) && lit->isPositive()) {
        if (lit->nthArgument(0)->term()->arity() == 1) {
          Literal *newlit = Literal::createEquality(true,
                                                    *lit->nthArgument(0)->term()->nthArgument(0),
                                                    *lit->nthArgument(1)->term()->nthArgument(0),
                                                    SortHelper::getArgSort(lit->nthArgument(0)->term(), 0));
          Clause* res = replaceLit(c, lit, newlit, SimplifyingInference1(InferenceRule::TERM_ALGEBRA_POSITIVE_INJECTIVITY_SIMPLIFYING, c));
          return res;
        }
      }
    }

    // no equalities between similar constructors were found
    return c;
  }

  bool NegativeInjectivityISE::litCondition(Clause *c, unsigned i)
  {
    Literal *lit = (*c)[i];
    if (sameConstructorsEquality(lit) && !lit->polarity()) {
      unsigned numTypeArguments = lit->nthArgument(0)->term()->numTypeArguments();
      unsigned arity = lit->nthArgument(0)->term()->arity();
      for (unsigned j = numTypeArguments; j < arity; j++) {
        Literal *l = Literal::createEquality(true,
                                             *lit->nthArgument(0)->term()->nthArgument(j),
                                             *lit->nthArgument(1)->term()->nthArgument(j),
                                             SortHelper::getArgSort(lit->nthArgument(0)->term(),j));
        for (unsigned k = 0; k < c->length(); k++) {
          if (k != i) {
            if (_salg->getOrdering().compare((*c)[k], l) != Ordering::GREATER) {
              return false;
            }
          }
        }
      }
      return true;
    }
    return false;
  }

  Clause* NegativeInjectivityISE::simplify(Clause *c)
  {
    if (c->isPureTheoryDescendant())
      return c;

    for (int i = c->length() - 1; i >= 0; i--) {
      if (litCondition(c, i)) {
        Literal *lit = (*c)[i];
        TermList lhs = *lit->nthArgument(0);
        ASS(lhs.isTerm());
        unsigned arity = lhs.term()->arity();
        unsigned numTypeArgs = lhs.term()->numTypeArguments();

        RStack<Literal*> resLits;
        Literal *newLit = Literal::createEquality(false,
                                                  *lit->nthArgument(0)->term()->nthArgument(numTypeArgs),
                                                  *lit->nthArgument(1)->term()->nthArgument(numTypeArgs),
                                                  SortHelper::getArgSort(lhs.term(), numTypeArgs));
        for (auto curr : c->iterLits()) {
          resLits->push(curr == lit ? newLit : curr);
        }
        
        for (unsigned j = numTypeArgs+1; j < arity; j++) {
          newLit = Literal::createEquality(false,
                                           *lit->nthArgument(0)->term()->nthArgument(j),
                                           *lit->nthArgument(1)->term()->nthArgument(j),
                                            SortHelper::getArgSort(lhs.term(), j));
          resLits->push(newLit);
        }

        return Clause::fromStack(*resLits,SimplifyingInference1(InferenceRule::TERM_ALGEBRA_NEGATIVE_INJECTIVITY_SIMPLIFYING, c));       
      }
    }
    return c;
  }

  void AcyclicityGIE::attach(SaturationAlgorithm* salg)
  {
    GeneratingInferenceEngine::attach(salg);

    _acyclIndex = static_cast<AcyclicityIndex*>(_salg->getIndexManager()->request(ACYCLICITY_INDEX));
  }

  void AcyclicityGIE::detach()
  {
    _acyclIndex = 0;
    _salg->getIndexManager()->release(ACYCLICITY_INDEX);
    GeneratingInferenceEngine::detach();
  }

  struct AcyclicityGIE::AcyclicityGenIterator
  {
    AcyclicityGenIterator(Clause *premise, Indexing::CycleQueryResultsIterator results)
      :
      _premise(premise),
      _queryResults(results)
    {}

    DECL_ELEMENT_TYPE(Clause *);

    bool hasNext() { return _queryResults.hasNext(); }
    
    OWN_ELEMENT_TYPE next()
    {
      Indexing::CycleQueryResult *qres = _queryResults.next();

      ASS_EQ(LiteralList::length(qres->literals), ClauseList::length(qres->premises));
      ASS_EQ(LiteralList::length(qres->literals), ClauseList::length(qres->clausesTheta));

      LiteralList::Iterator literals(qres->literals);
      ClauseList::Iterator premises(qres->premises);
      ClauseList::Iterator clausesTheta(qres->clausesTheta);
      
      UnitList* ulpremises = UnitList::empty();
      while (premises.hasNext()) {
        UnitList::push(premises.next(), ulpremises);
      }
      RStack<Literal*> resLits;

      premises.reset(qres->premises);

      while(literals.hasNext() && premises.hasNext() && clausesTheta.hasNext()) {
        Literal *l = literals.next();
        Clause *p = premises.next();
        Clause *c = clausesTheta.next();

        ASS_EQ(p->length(), c->length());

        for (unsigned j = 0; j < c->length(); j++) {
          if ((*p)[j] != l) {
            resLits->push((*c)[j]);
          }
        }
      }
      ASS (!literals.hasNext());
      ASS (!premises.hasNext());
      ASS (!clausesTheta.hasNext());

      auto res = Clause::fromStack(*resLits,GeneratingInferenceMany(InferenceRule::TERM_ALGEBRA_ACYCLICITY, ulpremises));
      // MS: to preserve the original semantics (although it looks slightly suspicious)
      res->setAge(_premise->age() + 1); 
      
      return res;
    }
  private:

    Clause *_premise;
    Indexing::CycleQueryResultsIterator _queryResults;
  };

  struct AcyclicityGIE::AcyclicityGenFn
  {
    AcyclicityGenFn(Indexing::AcyclicityIndex* aidx, Clause* premise)
      :
      _aidx(aidx),
      _premise(premise)
    {}
    VirtualIterator<Clause*> operator()(Literal* lit)
    {
      return pvi(AcyclicityGenIterator(_premise, _aidx->queryCycles(lit, _premise)));
    }
  private:
    Indexing::AcyclicityIndex *_aidx;
    Clause* _premise;
  };

  ClauseIterator AcyclicityGIE::generateClauses(Clause *c)
  {
    auto it1 = c->getSelectedLiteralIterator();
    auto it2 = getMappingIterator(it1, AcyclicityGenFn(_acyclIndex, c));
    auto it3 = getFlattenedIterator(it2);
    return pvi(it3);
  }

  void pushSubterms(TermList *tl, Stack<TermList*> &stack)
  {
    if (!termAlgebraConstructor(tl)) {
      return;
    }

    ASS(tl->isTerm());
    Term *t = tl->term();
    
    TermList sort = SortHelper::getResultSort(t);
    ASS(env.signature->isTermAlgebraSort(sort));

    if (env.signature->getTermAlgebraOfSort(sort)->allowsCyclicTerms()) {
      return;
    }

    Stack<Term*> toVisit;

    for (unsigned i = 0; i < t->arity(); i++) {
      if (SortHelper::getArgSort(t, i) == sort) {
        TermList *s = t->nthArgument(i);
        stack.push(s);
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
            stack.push(s);
            if (s->isTerm()) {
              toVisit.push(s->term());
            }
          }
        }
      }
    }
   
  }

  struct AcyclicityGIE1::SubtermDisequalityIterator
  {
    SubtermDisequalityIterator(Clause *clause, Literal *lit)
      :
      _clause(clause),
      _lit(lit),
      _subterms(0),
      _leftSide(false)
    {
      if (!lit->isEquality() || !lit->polarity()) {
        _leftSide = true;
      } else {
        _sort = SortHelper::getEqualityArgumentSort(_lit);
        pushSubterms(_lit->nthArgument(0), _subterms);
      }
    }

    DECL_ELEMENT_TYPE(Clause *);

    bool hasNext() {
      if (!_leftSide && _subterms.isEmpty()) {
        _leftSide = true;
        pushSubterms(_lit->nthArgument(1), _subterms);
      }
      return (_subterms.isNonEmpty());
    }
    
    OWN_ELEMENT_TYPE next()
    {
      Literal *newlit = Literal::createEquality(false,
                                                *_lit->nthArgument(_leftSide ? 0 : 1),
                                                *_subterms.pop(),
                                                _sort);
      return replaceLit(_clause, _lit, newlit, GeneratingInference1(InferenceRule::TERM_ALGEBRA_ACYCLICITY, _clause));
    }
        
  private:
    Clause *_clause;
    Literal *_lit;
    Stack<TermList*> _subterms;
    bool _leftSide;
    TermList _sort;
  };

  struct AcyclicityGIE1::SubtermDisequalityFn
  {
    SubtermDisequalityFn(Clause* premise)
      : _premise(premise) {}
    VirtualIterator<Clause*> operator()(Literal* lit)
    {
      return pvi(SubtermDisequalityIterator(_premise, lit));
    }
  private:
    Clause* _premise;
  };

  struct AcyclicityGIE1::LiteralIterator
  {
    LiteralIterator(Clause *clause)
      :
      _index(0),
      _length(clause->length()),
      _clause(clause)
    {}

    DECL_ELEMENT_TYPE(Literal *);

    bool hasNext() { return _index < _length; }

    OWN_ELEMENT_TYPE next() { return (*_clause)[_index++]; }

  private:
    unsigned _index;
    unsigned _length;
    Clause* _clause;
  };


  ClauseIterator AcyclicityGIE1::generateClauses(Clause* c)
  {
    LiteralIterator it1(c);
    auto it2 = getMappingIterator(it1, SubtermDisequalityFn(c));
    auto it3 = getFlattenedIterator(it2);
    return pvi(it3);
  }
 
}
