
/*
 * File TermAlgebraReasoning.cpp.
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
 * @file TermAlgebraReasoning.cpp
 */

#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Stack.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Statistics.hpp"

#include "TermAlgebraReasoning.hpp"

#include <cstring>

using namespace Kernel;
using namespace Lib;

namespace Inferences {

  // copy clause c, replacing literal a by b
  Clause* replaceLit(Clause *c, Literal *a, Literal *b, Inference *inf)
  {
    CALL("replaceLit");

    int length = c->length();
    Clause* res = new(length) Clause(length,
                                     c->inputType(),
                                     inf);

    unsigned i = 0;
    while ((*c)[i] != a) { i++; }
    std::memcpy(res->literals(), c->literals(), length * sizeof(Literal*));
    (*res)[i] = b;

    return res;
  }

  // copy clause c, with the exception of the ith literal
  Clause* removeLit(Clause *c, unsigned i, Inference *inf)
  {
    CALL("removeLit");

    unsigned length = c->length();
    ASS_GE(i, 0);
    ASS_L(i, length);

    Clause* res = new(length - 1) Clause(length - 1,
                                         c->inputType(),
                                         inf);

    std::memcpy(res->literals(), c->literals(), i * sizeof(Literal*));
    std::memcpy(res->literals() + i, c->literals() + i + 1, (length - i - 1) * sizeof(Literal*));

    return res;
  }

  // return f is the term has the form f(x1 ... xn) and f is a term
  // algebra constructor, or nullptr otherwise
  Signature::Symbol* termAlgebraConstructor(TermList *t)
  {
    CALL("termAlgebraConstructor");

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
    CALL("distinctConstructorsEquality");

    if (!lit->isEquality())
      return false;

    Signature::Symbol *s = termAlgebraConstructor(lit->nthArgument(0));
    Signature::Symbol *t = termAlgebraConstructor(lit->nthArgument(1));

    return (s && t && s != t);
  }

  // true iff the literal has the form f(x1 ... xn) =? f(y1 ... yn)
  // where f is a term algebra constructor
  bool sameConstructorsEquality(Literal *lit)
  {
    CALL("sameConstructorsEquality");

    if (!lit->isEquality())
      return false;

    Signature::Symbol *s = termAlgebraConstructor(lit->nthArgument(0));
    Signature::Symbol *t = termAlgebraConstructor(lit->nthArgument(1));

    return (s && s == t);
  }

  Clause* DistinctnessISE::simplify(Clause* c)
  {
    CALL("DistinctnessISE::simplify");

    if (c->isTheoryDescendant())
      return c;
    
    int length = c->length();
    for (int i = 0; i < length; i++) {
      Literal *lit = (*c)[i];
      if (distinctConstructorsEquality(lit)) {
        if (lit->isPositive()) {
          // equality of the form f(x) = g(y), delete literal from clause
          Clause* res = removeLit(c, i, new Inference1(Inference::TERM_ALGEBRA_DISTINCTNESS, c));
          res->setAge(c->age());
          env.statistics->taDistinctnessSimplifications++;
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
   * Given a clause f(x1, ..., xn) = y \/ A, this iterator returns the
   * clauses A { y <- g(z1, ..., zm) } for every constructor g (zi's
   * are fresh variables)
   */
  struct Distinctness1GIE::Distinctness1GenIterator
  {
    Distinctness1GenIterator(Clause *clause, Literal *lit)
      : _clause(clause),
        _lit(lit),
        _index(0),
        _varoccurs(false),
        _ta(nullptr)
    {
      ASS(_lit);

      if (_lit->polarity() && _lit->isEquality()) {
        if (_lit->nthArgument(0)->isVar() && termAlgebraConstructor(_lit->nthArgument(1))) {
          ASS(_lit->nthArgument(1)->isTerm());
          _functor = _lit->nthArgument(1)->term()->functor();
          _var = lit->nthArgument(0);
          _ta = env.signature->getTermAlgebraOfSort(SortHelper::getEqualityArgumentSort(_lit));
        } else if (_lit->nthArgument(1)->isVar() && termAlgebraConstructor(_lit->nthArgument(0))) {
          ASS(_lit->nthArgument(0)->isTerm());
          _functor = _lit->nthArgument(0)->term()->functor();
          _var = _lit->nthArgument(1);
          _ta = env.signature->getTermAlgebraOfSort(SortHelper::getEqualityArgumentSort(_lit));
        }
      }
      if (_ta && _ta->constructor(_index)->functor() == _functor) {
        _index++;
      }
    }

    DECL_ELEMENT_TYPE(Clause *);

    bool hasNext() { return (_ta && _index < _ta->nConstructors()); }
    OWN_ELEMENT_TYPE next()
    {
      CALL("Distinctness1GIE::Distinctness1GenIterator::next()");

      // create substitution sigma
      TermAlgebraConstructor* ctr = _ta->constructor(_index);
      unsigned freshVar = _clause->maxVar() + 1;
      Stack<TermList> args;
      Substitution subst;
      for (unsigned i = 0; i < ctr->arity(); i++) {
        args.push(TermList(freshVar + i, false));
      }
      subst.bind(_var->var(), Term::create(ctr->functor(), ctr->arity(), args.begin()));

      Inference *inf = new Inference1(Inference::TERM_ALGEBRA_DISTINCTNESS, _clause);
      unsigned length = _clause->length();
      Clause* res = new(length - 1) Clause(length - 1,
                                           _clause->inputType(),
                                           inf);
      unsigned j = 0;
      for (unsigned i = 0; i < length; i++) {
        if ((*_clause)[i] != _lit) {
          if ((*_clause)[i]->containsSubterm(*_var)) {
            _varoccurs = true;
            (*res)[j] = (*_clause)[i]->apply(subst);
          } else {
            (*res)[j] = (*_clause)[i];
          }
          j++;
        }
      }

      if (_varoccurs) {
        _index++;
        if (_index < _ta->nConstructors() && _ta->constructor(_index)->functor() == _functor) {
          // skip the constructor f
          _index++;
        }
      } else {
        // if x does not occurs in A, only one conclusion has to be generated
        _index = _ta->nConstructors();
      }
      res->setAge(_clause->age()+1);
      env.statistics->taDistinctness1Generations++;
      return res;
    }
  private:
    Clause *_clause;
    Literal *_lit;
    unsigned _index;
    bool _varoccurs; // whether x occurs in A
    unsigned _functor; // functor of f
    TermList* _var;
    TermAlgebra *_ta;
  };

  struct Distinctness1GIE::Distinctness1GenFn
  {
    Distinctness1GenFn(Clause* premise)
      :
      _premise(premise)
    {}
    
    DECL_RETURN_TYPE(VirtualIterator<Clause*>);

    OWN_RETURN_TYPE operator()(Literal* lit)
    {
      CALL("Distinctness1GIE::Distinctness1GenFn::operator()");

      return pvi(Distinctness1GenIterator(_premise, lit));
    }
  private:
    Clause* _premise;
  };

  ClauseIterator Distinctness1GIE::generateClauses(Clause* c)
  {
    CALL("Distinctness1GIE::generateClause");

    auto it1 = c->getSelectedLiteralIterator();
    auto it2 = getMappingIterator(it1, Distinctness1GenFn(c));
    auto it3 = getFlattenedIterator(it2);
    return pvi(it3);
  }

  void Distinctness2GIE::attach(SaturationAlgorithm* salg)
  {
    CALL("Distinctness2GIE::attach");

    GeneratingInferenceEngine::attach(salg);

    // TODO
  }

  void Distinctness2GIE::detach()
  {
    CALL("Distinctness2GIE::detach");

    // TODO
    
    GeneratingInferenceEngine::detach();
  }

  ClauseIterator Distinctness2GIE::generateClauses(Clause* c)
  {
    CALL("Distinctness2GIE::generateClause");

    // TODO
    return pvi(VirtualIterator<Clause*>::getEmpty());
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
        _type = env.signature->getFunction(lit->nthArgument(0)->term()->functor())->fnType();
        _length = lit->nthArgument(0)->term()->arity();
      } else {
        _length = 0;
      }
    }

    DECL_ELEMENT_TYPE(Clause *);

    bool hasNext() { return _index < _length; }
    OWN_ELEMENT_TYPE next()
    {
      CALL("InjectivityGIE::SubtermIterator::next()");

      Clause *res;
      Inference *inf = new Inference1(Inference::TERM_ALGEBRA_INJECTIVITY, _clause);
      
      
      // from the clause f(x1 ... xn) = f(y1 .. yn) \/ C, we create
      // a new clause xi = yi \/ C. In this case, next() can be
      // called n times to create the n relevant conclusions.
      Literal *l = Literal::createEquality(true,
                                           *_lit->nthArgument(0)->term()->nthArgument(_index),
                                           *_lit->nthArgument(1)->term()->nthArgument(_index),
                                           _type->arg(_index));
      
      res = replaceLit(_clause, _lit, l, inf);
      _index++;
      res->setAge(_clause->age()+1);
      env.statistics->taInjectivitySimplifications++;
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
    OperatorType* _type; // type of f
  };

  struct InjectivityGIE::SubtermEqualityFn
  {
    SubtermEqualityFn(Clause* premise)
      : _premise(premise) {}
    DECL_RETURN_TYPE(VirtualIterator<Clause*>);
    OWN_RETURN_TYPE operator()(Literal* lit)
    {
      CALL("InjectivityGIE::SubtermEqualityFn::operator()");

      return pvi(SubtermIterator(_premise, lit));
    }
  private:
    Clause* _premise;
  };

  ClauseIterator InjectivityGIE::generateClauses(Clause* c)
  {
    CALL("InjectivityGIE::generateClauses");

    auto it1 = c->getSelectedLiteralIterator();
    auto it2 = getMappingIterator(it1, SubtermEqualityFn(c));
    auto it3 = getFlattenedIterator(it2);
    return pvi(it3);
  }

  Clause* InjectivityISE::simplify(Clause *c)
  {
    CALL("InjectivityISE::simplify");
    
    if (c->isTheoryDescendant())
      return c;

    int length = c->length();
    for (int i = 0; i < length; i++) {
      Literal *lit = (*c)[i];
      if (lit->polarity() && sameConstructorsEquality(lit)) {
        if (lit->nthArgument(0)->term()->arity() == 1) {
          OperatorType *type = env.signature->getFunction(lit->nthArgument(0)->term()->functor())->fnType();
          Literal *newlit = Literal::createEquality(true,
                                                    *lit->nthArgument(0)->term()->nthArgument(0),
                                                    *lit->nthArgument(1)->term()->nthArgument(0),
                                                    type->arg(0));
          Clause* res = replaceLit(c, lit, newlit, new Inference1(Inference::TERM_ALGEBRA_INJECTIVITY, c));
          res->setAge(c->age());
          env.statistics->taInjectivitySimplifications++;
          return res;
        }
      }
    }

    // no equalities between similar constructors were found
    return c;
  }

    /*
   * Given a clause f(s1, ..., sn) = x \/ A, this iterator returns the
   * clauses (si = yi \/ A) { x <- f(y1, ..., yn) } for 0 <= i < n (yi's
   * are fresh variables)
   */
  struct Injectivity1GIE::Injectivity1GenIterator
  {
    Injectivity1GenIterator(Clause *clause, Literal *lit)
      : _clause(clause),
        _lit(lit),
        _index(0),
        _fx(nullptr),
        _tac(nullptr),
        _subst()
    {
      unsigned var;
      if (_lit->polarity() && _lit->isEquality()) {
        if (_lit->nthArgument(0)->isVar() && termAlgebraConstructor(_lit->nthArgument(1))) {
          _fx = _lit->nthArgument(1);
          var = _lit->nthArgument(0)->var();
        } else if (_lit->nthArgument(1)->isVar() && termAlgebraConstructor(_lit->nthArgument(0))) {
          ASS(_lit->nthArgument(0)->isTerm());
          _fx = _lit->nthArgument(0);
          var = _lit->nthArgument(1)->var();
        }
      }
      if (_fx) {
        ASS(_fx->isTerm());
        _tac = env.signature->getTermAlgebraConstructor(_fx->term()->functor());

        // create substitution sigma
        _freshVar = _clause->maxVar() + 1;
        Stack<TermList> args;
        for (unsigned i = 0; i < _tac->arity(); i++) {
          args.push(TermList(_freshVar + i, false));
        }
        _subst.bind(var, Term::create(_tac->functor(), _tac->arity(), args.begin()));

        // compute A\sigma
        unsigned length = _clause->length();
        _asigma = new(length) Clause(length,
                                     _clause->inputType(),
                                     new Inference1(Inference::TERM_ALGEBRA_INJECTIVITY, _clause));
        
        for (unsigned i = 0; i < length; i++) {
          if ((*_clause)[i] == _lit) {
            (*_asigma)[i] = _lit;
          } else {
            (*_asigma)[i] = (*_clause)[i]->apply(_subst);
          }
        }
      }
    }

    ~Injectivity1GenIterator() {
      // TODO deallocate asigma
    }

    DECL_ELEMENT_TYPE(Clause *);

    bool hasNext() { return (_tac && _index < _tac->arity()); }
    OWN_ELEMENT_TYPE next()
    {
      CALL("Injectivity1GIE::Injectivity1GenIterator::next()");

      Inference *inf = new Inference1(Inference::TERM_ALGEBRA_INJECTIVITY, _clause);
      Literal* newLit = Literal::createEquality(true,
                                                TermList(_freshVar + _index, false),
                                                *_fx->term()->nthArgument(_index),
                                                _tac->argSort(_index));
      Clause* res = replaceLit(_asigma, _lit, newLit->apply(_subst), inf);
      _index++;
      res->setAge(_clause->age()+1);
      env.statistics->taInjectivity1Generations++;
      return res;
    }
  private:
    Clause *_clause;
    Literal *_lit;
    unsigned _index;
    TermList* _fx;
    TermAlgebraConstructor *_tac;
    unsigned _freshVar;
    Substitution _subst;
    Clause *_asigma;
    unsigned _litpos;
  };

  struct Injectivity1GIE::Injectivity1GenFn
  {
    Injectivity1GenFn(Clause* premise)
      :
      _premise(premise)
    {}
    
    DECL_RETURN_TYPE(VirtualIterator<Clause*>);

    OWN_RETURN_TYPE operator()(Literal* lit)
    {
      CALL("Injectivity1GIE::Injectivity1GenFn::operator()");

      return pvi(Injectivity1GenIterator(_premise, lit));
    }
  private:
    Clause* _premise;
  };

  ClauseIterator Injectivity1GIE::generateClauses(Clause* c)
  {
    CALL("Injectivity1GIE::generateClause");

    auto it1 = c->getSelectedLiteralIterator();
    auto it2 = getMappingIterator(it1, Injectivity1GenFn(c));
    auto it3 = getFlattenedIterator(it2);
    return pvi(it3);
  }

  void Injectivity2GIE::attach(SaturationAlgorithm* salg)
  {
    CALL("Injectivity2GIE::attach");

    GeneratingInferenceEngine::attach(salg);

    // TODO
  }

  void Injectivity2GIE::detach()
  {
    CALL("Injectivity2GIE::detach");
    ASS(_salg);

    // TODO
    GeneratingInferenceEngine::detach();
  }

  ClauseIterator Injectivity2GIE::generateClauses(Clause* c)
  {
    CALL("Injectivity2GIE::generateClause");

    // TODO
    return pvi(VirtualIterator<Clause*>::getEmpty());
  }

  bool NegativeInjectivityISE::litCondition(Clause *c, unsigned i) {
    Literal *lit = (*c)[i];
    if (!lit->polarity() && sameConstructorsEquality(lit)) {
      unsigned arity = lit->nthArgument(0)->term()->arity();
      OperatorType *type = env.signature->getFunction(lit->nthArgument(0)->term()->functor())->fnType();
      for (unsigned j = 0; j < arity; j++) {
        Literal *l = Literal::createEquality(true,
                                             *lit->nthArgument(0)->term()->nthArgument(j),
                                             *lit->nthArgument(1)->term()->nthArgument(j),
                                             type->arg(j));
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
    CALL("NegativeInjectivityISE::simplify");

    if (c->isTheoryDescendant())
      return c;

    int length = c->length();
    for (int i = 0; i < length; i++) {
      if (litCondition(c, i)) {
        Literal *lit = (*c)[i];
        OperatorType *type = env.signature->getFunction(lit->nthArgument(0)->term()->functor())->fnType();
        unsigned oldLength = c->length();
        unsigned arity = lit->nthArgument(0)->term()->arity();
        unsigned newLength = oldLength + arity - 1;
        Clause* res = new(newLength) Clause(newLength,
                                            c->inputType(),
                                            new Inference1(Inference::TERM_ALGEBRA_INJECTIVITY, c));
        Literal *newLit = Literal::createEquality(false,
                                                  *lit->nthArgument(0)->term()->nthArgument(0),
                                                  *lit->nthArgument(1)->term()->nthArgument(0),
                                                  type->arg(0));
        unsigned i = 0;
        while ((*c)[i] != lit) { i++; }
        std::memcpy(res->literals(), c->literals(), length * sizeof(Literal*));
        (*res)[i] = newLit;
        
        for (unsigned i = 1; i < arity; i++) {
          newLit = Literal::createEquality(false,
                                           *lit->nthArgument(0)->term()->nthArgument(i),
                                           *lit->nthArgument(1)->term()->nthArgument(i),
                                           type->arg(i));
          (*res)[oldLength + i - 1] = newLit;
        }
        res->setAge(c->age());
        env.statistics->taNegativeInjectivitySimplifications++;

        return res;
      }
    }
    return c;
  }

  void AcyclicityGIE::attach(SaturationAlgorithm* salg)
  {
    CALL("AcyclicityGIE::attach");

    GeneratingInferenceEngine::attach(salg);

    _acyclIndex = static_cast<AcyclicityIndex*>(_salg->getIndexManager()->request(ACYCLICITY_INDEX));
  }

  void AcyclicityGIE::detach()
  {
    CALL("AcyclicityGIE::detach");

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
      CALL("AcyclicityGIE::AcyclicityGenIterator::next()");

      Indexing::CycleQueryResult *qres = _queryResults.next();

      ASS_EQ(LiteralList::length(qres->literals), ClauseList::length(qres->premises));
      ASS_EQ(LiteralList::length(qres->literals), ClauseList::length(qres->clausesTheta));

      LiteralList::Iterator literals(qres->literals);
      ClauseList::Iterator premises(qres->premises);
      ClauseList::Iterator clausesTheta(qres->clausesTheta);
      
      unsigned length = qres->totalLengthClauses() - LiteralList::length(qres->literals);
      UnitList* ulpremises = UnitList::empty();
      while (premises.hasNext()) {
        UnitList::push(premises.next(), ulpremises);
      }
      Inference* inf = new InferenceMany(Inference::TERM_ALGEBRA_ACYCLICITY, ulpremises);
      Clause* res = new(length) Clause(length,
                                       _premise->inputType(),
                                       inf);

      premises.reset(qres->premises);
      unsigned i = 0;
      unsigned maxVar = 0;

      while(literals.hasNext() && premises.hasNext() && clausesTheta.hasNext()) {              
        Literal *l = literals.next();
        Clause *p = premises.next();
        Clause *c = clausesTheta.next();

        ASS_EQ(p->length(), c->length());

        for (unsigned j = 0; j < c->length(); j++) {
          if ((*p)[j] != l) {
            (*res)[i++] = (*c)[j];
          }
        }

        maxVar++;
      }
      ASS (!literals.hasNext());
      ASS (!premises.hasNext());
      ASS (!clausesTheta.hasNext());
      ASS_EQ(i, length);

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
    DECL_RETURN_TYPE(VirtualIterator<Clause*>);
    OWN_RETURN_TYPE operator()(Literal* lit)
    {
      CALL("AcyclicityGIE::AyclicityGenFn::operator()");

      return pvi(AcyclicityGenIterator(_premise, _aidx->queryCycles(lit, _premise)));
    }
  private:
    Indexing::AcyclicityIndex *_aidx;
    Clause* _premise;
  };

  ClauseIterator AcyclicityGIE::generateClauses(Clause *c)
  {
    CALL("AcyclicityGIE::generateClauses");

    auto it1 = c->getSelectedLiteralIterator();
    auto it2 = getMappingIterator(it1, AcyclicityGenFn(_acyclIndex, c));
    auto it3 = getFlattenedIterator(it2);
    return pvi(it3);
  }

  void pushSubterms(TermList *tl, Stack<TermList*> &stack)
  {
    CALL("getSubterms");

    if (!termAlgebraConstructor(tl)) {
      return;
    }

    ASS(tl->isTerm());
    Term *t = tl->term();
    
    unsigned sort = SortHelper::getResultSort(t);
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
      CALL("InjectivityGIE::SubtermIterator::next()");

      Literal *newlit = Literal::createEquality(false,
                                                *_lit->nthArgument(_leftSide ? 0 : 1),
                                                *_subterms.pop(),
                                                _sort);
      Clause* res = replaceLit(_clause, _lit, newlit, new Inference1(Inference::TERM_ALGEBRA_ACYCLICITY, _clause));
      res->setAge(_clause->age() + 1);
      env.statistics->taAcyclicityGeneratedDisequalities++;
      return res;
    }
        
  private:
    Clause *_clause;
    Literal *_lit;
    Stack<TermList*> _subterms;
    bool _leftSide;
    unsigned _sort;
  };

  struct AcyclicityGIE1::SubtermDisequalityFn
  {
    SubtermDisequalityFn(Clause* premise)
      : _premise(premise) {}
    DECL_RETURN_TYPE(VirtualIterator<Clause*>);
    OWN_RETURN_TYPE operator()(Literal* lit)
    {
      CALL("AcyclicityGIE1::SubtermDisequalityFn::operator()");

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
    CALL("AcyclicityGIE1::generateClauses");

    LiteralIterator it1(c);
    auto it2 = getMappingIterator(it1, SubtermDisequalityFn(c));
    auto it3 = getFlattenedIterator(it2);
    return pvi(it3);
  }

  Clause* InfinitenessISE::simplify(Clause* c)
  {
    CALL("InfinitenessISE::simplify");

    if (c->isTheoryDescendant()) {
      return c;
    }

    bool *pos = nullptr;
    Clause *r = nullptr;
    
    int length = c->length();
    for (int i = 0; i < length; i++) {
      Literal *lit = (*c)[i];

      if (lit->isEquality() && lit->isPositive()) {
        unsigned s = SortHelper::getEqualityArgumentSort(lit);
        if (env.signature->isTermAlgebraSort(s)) {
          TermAlgebra* ta = env.signature->getTermAlgebraOfSort(s);
          if (ta->infiniteDomain()) {
            if (!pos) {
              pos = static_cast<bool*>ALLOC_KNOWN(c->length() * sizeof(bool), "InfinitenessISE::simplify::pos");
            }
            if (lit->nthArgument(0)->isVar() && (r = deleteLits(c, lit->nthArgument(0), pos))) {
              goto ret;
            }
            if (lit->nthArgument(1)->isVar() && (r = deleteLits(c, lit->nthArgument(1), pos))) {
              goto ret;
            }
          }
        }
      }
    }
    // no deletable literals found, return unsimplified clause
    r = c;

  ret:
    if (pos) {
      DEALLOC_KNOWN(pos, c->length() * sizeof(bool), "InfinitenessISE::simplify::pos");
    }
    return r;
  }

  Clause* InfinitenessISE::deleteLits(Kernel::Clause* c, TermList* var, bool* positions)
  {
    CALL("InfinitenessISE::deleteLits");
    ASS(var->isVar());

    unsigned toDelete = 0;
    unsigned length = c->length();
    
    for (unsigned i = 0; i < length; i++) {
      Literal *lit = (*c)[i];

      if (lit->isEquality()) {
        TermList *s = lit->nthArgument(0);
        TermList *t = lit->nthArgument(1);
        if (s->isTerm() && s->containsSubterm(*var)) {
          return nullptr;
        }
        if (t->isTerm() && t->containsSubterm(*var)) {
          return nullptr;
        }
        positions[i] = lit->isPositive() && (TermList::equals(*s, *var) || TermList::equals(*t, *var));
        toDelete += positions[i];
      } else {
        if (lit->containsSubterm(*var)) {
          return nullptr;
        }
      }
    }

    if (toDelete == 0) {
      return nullptr;
    } else {
      unsigned resLength = length - toDelete;
      Clause* res = new(resLength) Clause(resLength,
                                          c->inputType(),
                                          new Inference1(Inference::TERM_ALGEBRA_INFINITENESS, c));
      unsigned i = 0;
      for (unsigned j = 0; j < length; j++) {
        if (!positions[j]) {
          (*res)[i] = (*c)[j];
          i++;
        }
      }
      res->setAge(c->age());
      env.statistics->taInfinitenessSimplifications++;
      return res;
    }
  }
 
}
