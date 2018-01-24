
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


#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/SmartPtr.hpp"
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
    : IteratorCore<Clause*>
  {
    CLASS_NAME(Distinctness1GenIterator);
    USE_ALLOCATOR(Distinctness1GenIterator);
    
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
          _var = _lit->nthArgument(0)->var();
          _ta = env.signature->getTermAlgebraOfSort(SortHelper::getEqualityArgumentSort(_lit));
        } else if (_lit->nthArgument(1)->isVar() && termAlgebraConstructor(_lit->nthArgument(0))) {
          ASS(_lit->nthArgument(0)->isTerm());
          _functor = _lit->nthArgument(0)->term()->functor();
          _var = _lit->nthArgument(1)->var();
          _ta = env.signature->getTermAlgebraOfSort(SortHelper::getEqualityArgumentSort(_lit));
        }
      }
      if (_ta && _ta->constructor(_index)->functor() == _functor) {
        _index++;
      }
    }

    bool hasNext() { return (_ta && _index < _ta->nConstructors()); }

    Clause* next()
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
      subst.bind(_var, Term::create(ctr->functor(), ctr->arity(), args.begin()));

      Inference *inf = new Inference1(Inference::TERM_ALGEBRA_DISTINCTNESS, _clause);
      unsigned length = _clause->length();
      Clause* res = new(length - 1) Clause(length - 1,
                                           _clause->inputType(),
                                           inf);
      unsigned j = 0;
      for (unsigned i = 0; i < length; i++) {
        if ((*_clause)[i] != _lit) {
          if (IntList::member(_var, (*_clause)[i]->freeVariables())) {
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
    unsigned _var;
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

      return vi(new Distinctness1GenIterator(_premise, lit));
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

  // declaring an IteratorCore rather than an ordering iterator class
  // avoid calling the copy constructor to build a
  // VirtualIterator. Saves a copy, but more importantly avoids
  // deallocating memory twice in destructors
  struct DistAndInj2GIE::Injectivity2Iterator
    : IteratorCore<Clause*>
  {
    CLASS_NAME(Injectivity2Iterator);
    USE_ALLOCATOR(Injectivity2Iterator);
    
    Injectivity2Iterator(Clause *c1, Clause *c2,
                         Literal *lit1, Literal *lit2,
                         TermList f1, TermList f2,
                         ResultSubstitutionSP sigma)
      :
      _c1(c1),
      _c2(c2),
      _index(0),
      _functor(f1.term()->functor()),
      _arity(env.signature->getFunction(_functor)->arity()),
      _age(Int::max(c1->age(), c2->age()) + 1),
      _sigma(sigma),
      _f1(f1),
      _f2(f2)
    {
      ASS(_f1.isTerm());
      ASS(_f2.isTerm());
      ASS_EQ(_f1.term()->functor(), _f2.term()->functor());

      // pre-compute the common part of the conclusions
      _length = c1->length() + c2->length() - 1;
      unsigned i = 0;
      if (_length > 1) {
        _csigma = (Literal**)ALLOC_KNOWN((_length - 1) * sizeof(Literal*), "Injectivity2Iterator::csigma");

        for (unsigned j = 0; j < c1->length(); j++) {
          if ((*c1)[j] != lit1) {
            _csigma[i++] = sigma->applyToQuery((*c1)[j]);
          }
        }
        for (unsigned j = 0; j < c2->length(); j++) {
          if ((*c2)[j] != lit2) {
            _csigma[i++] = sigma->applyToResult((*c2)[j]);
          }
        }
      } else {
        _csigma = nullptr;
      }
      ASS_EQ(i, _length - 1);
    }

    ~Injectivity2Iterator()
    {
      if (_csigma) {
        DEALLOC_KNOWN(_csigma, (_length - 1) * sizeof(Literal*), "Injectivity2Iterator::csigma");
      }
    }

    bool hasNext() { return _index < _arity; }

    Clause* next() {
      CALL("Injectivity2Iterator::next()");
      ASS_L(_index, _f1.term()->arity());
      ASS_L(_index, _f2.term()->arity());     

      Literal * newLit = Literal::createEquality(true,
                                                 _sigma->applyToQuery(*_f1.term()->nthArgument(_index)),
                                                 _sigma->applyToResult(*_f2.term()->nthArgument(_index)),
                                                 env.signature->getFunction(_functor)->fnType()->arg(_index));
      Clause* res = new(_length) Clause(_length,
                                        _c1->inputType(),
                                        new Inference2(Inference::TERM_ALGEBRA_INJECTIVITY, _c1, _c2));
      if (_csigma) {
        std::memcpy(res->literals(), _csigma, (_length - 1) * sizeof(Literal*));
      }
      (*res)[_length - 1] = newLit;
      res->setAge(_age);
      env.statistics->taInjectivity2Generations++;
      _index++;
      return res;
    }

  private:
    Clause* _c1;
    Clause* _c2;
    unsigned _index;
    unsigned _functor;
    unsigned _arity;
    unsigned _age;
    ResultSubstitutionSP _sigma;
    Literal** _csigma;
    unsigned _length;
    TermList _f1;
    TermList _f2;
  };

  struct DistAndInj2GIE::DistAndInj2PerformFn
  {
    DistAndInj2PerformFn(Clause* premise, Literal *lit, TermList lhs, TermList rhs, Ordering& ord)
      :
      _premise(premise),
      _lit(lit),
      _lhs(lhs),
      _rhs(rhs),
      _ord(ord)
    {
      ASS(lit->isEquality());
    }

    DECL_RETURN_TYPE(VirtualIterator<Clause*>);
    
    OWN_RETURN_TYPE operator()(TermQueryResult tqr)
    {
      CALL("DistAndInj2GIE::DistAndInj2PerformFn::operator()");
      
      // premises must be distinct, otherwise the conclusion is redundant
      Clause *premise2 = tqr.clause;
      
      if (premise2 == _premise) {
        return VirtualIterator<Clause*>::getEmpty();
      }

      ASS(tqr.literal->isEquality());
      if (SortHelper::getEqualityArgumentSort(_lit) != SortHelper::getEqualityArgumentSort(tqr.literal)) {
        // despite the unification, this can happen
        // probably if the unified term is a variable?
        return VirtualIterator<Clause*>::getEmpty();
      }

      // check ordering contrainst after substitution
      if (Ordering::isGorGEorE(_ord.compare(tqr.substitution->applyToQuery(_rhs),
                                            tqr.substitution->applyToQuery(_lhs)))) {
        return VirtualIterator<Clause*>::getEmpty();
      }
      // same thing in the target clause
      TermList rhs2 = tqr.term;
      TermList lhs2 = EqHelper::getOtherEqualitySide(tqr.literal, rhs2);
      if (Ordering::isGorGEorE(_ord.compare(tqr.substitution->applyToResult(rhs2),
                                            tqr.substitution->applyToResult(lhs2)))) {
        return VirtualIterator<Clause*>::getEmpty();
      }

      if (_lhs.term()->functor() == lhs2.term()->functor()) {
        return vi(new Injectivity2Iterator(_premise, premise2, _lit, tqr.literal, _lhs, lhs2, tqr.substitution));
      } else {
        Clause *c = distinctnessConclusion(_premise, premise2, _lit, tqr.literal, tqr.substitution);
        return pvi(getSingletonIterator(c));
      }
    }

  private:
    Clause* _premise;
    Literal* _lit;
    TermList _lhs;
    TermList _rhs;
    Ordering& _ord;
  };

  Clause* DistAndInj2GIE::distinctnessConclusion(Clause *c1, Clause *c2,
                                                 Literal *lit1, Literal *lit2,
                                                 ResultSubstitutionSP sigma)
  {
    CALL("DistAndInj2GIE::distinctnessConclusion");

    ASS_EQ(SortHelper::getEqualityArgumentSort(lit1),
           SortHelper::getEqualityArgumentSort(lit2));

    unsigned length1 = c1->length();
    unsigned length2 = c2->length();
    Clause* res = new(length1 + length2 - 2) Clause(length1 + length2 - 2,
                                                    c1->inputType(),
                                                    new Inference2(Inference::TERM_ALGEBRA_DISTINCTNESS, c1, c2));
      
    unsigned i = 0;
    for (unsigned j = 0; j < length1; j++) {
      if ((*c1)[j] != lit1) {
        (*res)[i++] = sigma->applyToQuery((*c1)[j]);
      }
    }
    for (unsigned j = 0; j < length2; j++) {
      if ((*c2)[j] != lit2) {
        (*res)[i++] = sigma->applyToResult((*c2)[j]);
      }
    }
    ASS_EQ(i, length1 + length2 - 2);
    res->setAge(Int::max(c1->age(), c2->age()) + 1);
    env.statistics->taDistinctness2Generations++;
      
    return res;
  }

  struct DistAndInj2GIE::DistAndInj2GenFn
  {
    DistAndInj2GenFn(Clause* premise, Ordering& ord, TARulesRHSIndex* index)
      :
      _premise(premise),
      _ord(ord),
      _index(index)
    {}

    DECL_RETURN_TYPE(VirtualIterator<Clause*>);

    OWN_RETURN_TYPE operator()(Literal* lit)
    {
      CALL("DistAndInj2GIE::DistAndInj2GenFn::operator()");

      TermList *lhs, *rhs;
      if (Indexing::TARulesRHSIndex::rhsEligible(lit, _ord, lhs, rhs)) {
        auto it1 = _index->getUnifications(*rhs, true);
        auto it2 = getMappingIterator(it1, DistAndInj2PerformFn(_premise, lit, *lhs, *rhs, _ord));
        auto it3 = getFlattenedIterator(it2);
        return pvi(it3);
      }
      return pvi(VirtualIterator<Clause*>::getEmpty());
    }
    
  private:
    Clause* _premise;
    Ordering &_ord;
    TARulesRHSIndex* _index;
  };

  void DistAndInj2GIE::attach(SaturationAlgorithm* salg)
  {
    CALL("DistAndInj2GIE::attach");

    GeneratingInferenceEngine::attach(salg);
    _index = static_cast<TARulesRHSIndex*>(_salg->getIndexManager()->request(TA_RULES_RHS_INDEX) );
  }

  void DistAndInj2GIE::detach()
  {
    CALL("DistAndInj2GIE::detach");

    _index = nullptr;
    _salg->getIndexManager()->release(TA_RULES_RHS_INDEX);
    GeneratingInferenceEngine::detach();
  }

  ClauseIterator DistAndInj2GIE::generateClauses(Clause* c)
  {
    CALL("DistAndInj2GIE::generateClause");

    auto it1 = c->getSelectedLiteralIterator();
    auto it2 = getMappingIterator(it1, DistAndInj2GenFn(c, _salg->getOrdering(), _index));
    auto it3 = getFlattenedIterator(it2);
    return pvi(it3);
  }

  /*
   * Given a clause f(x1, ..., xn) = f(y1, ... yn) \/ A, this iterator
   * returns the clauses x1 = y1 \/ A up to xn = yn \/ A. For any
   * other literal the iterator is empty
   */
  struct InjectivityGIE::SubtermIterator
    : IteratorCore<Clause*>
  {
    CLASS_NAME(SubtermIterator);
    USE_ALLOCATOR(SubtermIterator);
    
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

    bool hasNext() { return _index < _length; }

    Clause* next()
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

      return vi(new SubtermIterator(_premise, lit));
    }
  private:
    Clause* _premise;
  };

  ClauseIterator InjectivityGIE::generateClauses(Clause* c)
  {
    CALL("InjectivityGIE::generateClauses");

    // TODO delete premise?

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
    : public IteratorCore<Clause*>
  {
    CLASS_NAME(Injectivity1GenIterator);
    USE_ALLOCATOR(Injectivity1GenIterator);
    
    Injectivity1GenIterator(Clause *clause, Literal *lit)
      : _clause(clause),
        _index(0),
        _fx(nullptr),
        _tac(nullptr),
        _subst(),
        _length(_clause->length())
    {
      ASS(clause);
      ASS(lit);
      
      unsigned var;
      if (lit->polarity() && lit->isEquality()) {
        if (lit->nthArgument(0)->isVar() && termAlgebraConstructor(lit->nthArgument(1))) {
          _fx = lit->nthArgument(1)->term();
          var = lit->nthArgument(0)->var();
        } else if (lit->nthArgument(1)->isVar() && termAlgebraConstructor(lit->nthArgument(0))) {
          ASS(lit->nthArgument(0)->isTerm());
          _fx = lit->nthArgument(0)->term();
          var = lit->nthArgument(1)->var();
        }
      }
      if (_fx) {
        _tac = env.signature->getTermAlgebraConstructor(_fx->functor());

        // create substitution sigma
        _freshVar = _clause->maxVar() + 1;
        Stack<TermList> args;
        for (unsigned i = 0; i < _tac->arity(); i++) {
          args.push(TermList(_freshVar + i, false));
        }
        _subst.bind(var, Term::create(_tac->functor(), _tac->arity(), args.begin()));

        // compute the common part of the conclusions
        _asigma = (Literal**)ALLOC_KNOWN(_length * sizeof(Literal*), "Injectivity1GenIterator::asigma");
        
        for (unsigned i = 0; i < _length; i++) {
          if ((*_clause)[i] == lit) {
            _asigma[i] = lit;
            _litpos = i;
          } else {
            _asigma[i] = (*_clause)[i]->apply(_subst);
          }
        }
      } else {
        _asigma = nullptr;
      }
    }

    ~Injectivity1GenIterator() {
      if (_asigma) {
        DEALLOC_KNOWN(_asigma, _length * sizeof(Literal*), "Injectivity1GenIterator::asigma");
      }
    }

    bool hasNext() { return (_tac && _index < _tac->arity()); }
    
    Clause* next()
    {
      CALL("Injectivity1GIE::Injectivity1GenIterator::next()");

      Inference *inf = new Inference1(Inference::TERM_ALGEBRA_INJECTIVITY, _clause);
      Literal* newLit = Literal::createEquality(true,
                                                TermList(_freshVar + _index, false),
                                                *_fx->nthArgument(_index),
                                                _tac->argSort(_index));
      unsigned length = _clause->length();
      Clause* res = new(length) Clause(length,
                                       _clause->inputType(),
                                       inf);
      
      std::memcpy(res->literals(), _asigma, length * sizeof(Literal*));
      (*res)[_litpos] = newLit->apply(_subst);
      
      _index++;
      res->setAge(_clause->age()+1);
      env.statistics->taInjectivity1Generations++;
      return res;
    }
  private:
    Clause *_clause;
    unsigned _index;
    Term* _fx;
    TermAlgebraConstructor *_tac;
    unsigned _freshVar;
    Substitution _subst;
    Literal **_asigma;
    unsigned _litpos;
    unsigned _length;
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

      return vi(new Injectivity1GenIterator(_premise, lit));
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
    _chainIndex = static_cast<ChainIndex*>(_salg->getIndexManager()->request(CHAIN_INDEX));
  }

  void AcyclicityGIE::detach()
  {
    CALL("AcyclicityGIE::detach");

    _chainIndex = nullptr;
    _salg->getIndexManager()->release(CHAIN_INDEX);
    GeneratingInferenceEngine::detach();
  }

  struct AcyclicityGIE::AcyclicityGenIterator
    : IteratorCore<Clause*>
  {
    CLASS_NAME(AcyclicityGenIterator);
    USE_ALLOCATOR(AcyclicityGenIterator);
    
    AcyclicityGenIterator(Clause *premise, VirtualIterator<Indexing::ChainQueryResult> results)
      :
      _premise(premise),
      _queryResults(results)
    {}

    bool hasNext() { return _queryResults.hasNext(); }
    
    Clause* next()
    {
      CALL("AcyclicityGIE::AcyclicityGenIterator::next()");

      Indexing::ChainQueryResult qres = _queryResults.next();

      ASS_EQ(LiteralList::length(qres.literals), ClauseList::length(qres.premises));
      ASS_EQ(LiteralList::length(qres.literals), ClauseList::length(qres.clausesTheta));

      LiteralList::Iterator literals(qres.literals);
      ClauseList::Iterator premises(qres.premises);
      ClauseList::Iterator clausesTheta(qres.clausesTheta);
      
      unsigned length = qres.totalLengthClauses() - LiteralList::length(qres.literals) + (qres.isCycle ? 0 : 1);
      UnitList* ulpremises = UnitList::empty();
      while (premises.hasNext()) {
        UnitList::push(premises.next(), ulpremises);
      }
      Inference* inf = new InferenceMany(Inference::TERM_ALGEBRA_ACYCLICITY, ulpremises);
      Clause* res = new(length) Clause(length,
                                       _premise->inputType(),
                                       inf);

      premises.reset(qres.premises);
      unsigned i = 0;

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
      }

      if (!qres.isCycle) {
        TermAlgebra* ta1 = env.signature->getTermAlgebraOfSort(qres.term1sort);
        TermAlgebra* tan = env.signature->getTermAlgebraOfSort(qres.termnsort);
        unsigned pred = tan->getSubtermPredicate(ta1);
        (*res)[i++] = Literal::create2(pred, false, qres.term1, qres.termn);
      }
      
      ASS (!literals.hasNext());
      ASS (!premises.hasNext());
      ASS (!clausesTheta.hasNext());
      ASS_EQ(i, length);

      res->setAge(_premise->age() + 1);
      env.statistics->taAcyclicityResolution++;
      return res;
    }
  private:

    Clause *_premise;
    Lib::VirtualIterator<Indexing::ChainQueryResult> _queryResults;
  };

  struct AcyclicityGIE::AcyclicityGenFn
  {
    AcyclicityGenFn(Indexing::ChainIndex* cidx, Clause* premise)
      :
      _cidx(cidx),
      _premise(premise)
    {}
    DECL_RETURN_TYPE(VirtualIterator<Clause*>);
    OWN_RETURN_TYPE operator()(Literal* lit)
    {
      CALL("AcyclicityGIE::AyclicityGenFn::operator()");

      return vi(new AcyclicityGenIterator(_premise, _cidx->queryChains(lit, _premise, false)));
    }
  private:
    Indexing::ChainIndex *_cidx;
    Clause* _premise;
  };

  ClauseIterator AcyclicityGIE::generateClauses(Clause *c)
  {
    CALL("AcyclicityGIE::generateClauses");

    auto it1 = c->getSelectedLiteralIterator();
    auto it2 = getMappingIterator(it1, AcyclicityGenFn(_chainIndex, c));
    auto it3 = getFlattenedIterator(it2);
    return pvi(it3);
  }

  void UniquenessGIE::attach(SaturationAlgorithm* salg)
  {
    CALL("UniquenessGIE::attach");

    GeneratingInferenceEngine::attach(salg);
    _chainIndex = static_cast<ChainIndex*>(_salg->getIndexManager()->request(CHAIN_INDEX));
  }

  void UniquenessGIE::detach()
  {
    CALL("UniquenessGIE::detach");

    _chainIndex = nullptr;
    _salg->getIndexManager()->release(CHAIN_INDEX);
    GeneratingInferenceEngine::detach();
  }

  struct UniquenessGIE::UniquenessGenIterator
    : IteratorCore<Clause*>
  {
    CLASS_NAME(UniquenessGenIterator);
    USE_ALLOCATOR(UniquenessGenIterator);
    
    UniquenessGenIterator(Clause *premise, VirtualIterator<Indexing::ChainQueryResult> results)
      :
      _premise(premise),
      _queryResults(results)
    {}

    bool hasNext() { return _queryResults.hasNext(); }

    TermList makeContext(TermList t, unsigned tsort,
                         TermList::Position* pos,
                         TermList x,
                         ChainQueryResult qres,
                         unsigned* freshVar, LiteralList*& sideConditions)
    {
      CALL("UniquenessGIE::UniquenessGenIterator::makeContext");

      if (TermList::Position::isEmpty(pos)) {
        TermAlgebra* ta1 = env.signature->getTermAlgebraOfSort(qres.term1sort);
        TermAlgebra* tan = env.signature->getTermAlgebraOfSort(tsort);
        if (tan && ta1->isMutualType(tan)) {
          unsigned appFun = tan->getAppFunction(ta1); // TODO sort might be wrong
          TermList y(*freshVar++, false);
          Literal *sc = Literal::createEquality(false,
                                                t,
                                                TermList(Term::create2(appFun, y, qres.term1)),
                                                tsort);
          LiteralList::push(sc, sideConditions);
          return TermList(Term::create2(appFun, y, x));
        } else {
          return t;
        }
      } else {
        // recursive case
        ASS(t.isTerm());
        ASS_L(pos->head(), t.term()->arity());
        Term *term = t.term();

        Stack<TermList> args;
        for (unsigned i = 0; i < term->arity(); i++) {
          unsigned argSort = SortHelper::getArgSort(term, i);
          if (i == pos->head()) {
            args.push(makeContext(*term->nthArgument(i), argSort, pos->tail(), x, qres, freshVar, sideConditions));
          } else {
            // call with empty position to trigger the base case
            args.push(makeContext(*term->nthArgument(i), argSort, TermList::Position::empty(), x, qres, freshVar, sideConditions));
          }
        }
        return TermList(Term::create(t.term()->functor(), t.term()->arity(), args.begin()));
      }
    }
    
    Clause* next()
    {
      CALL("UniquenessGIE::UniquenessGenIterator::next()");

      Indexing::ChainQueryResult qres = _queryResults.next();

      ASS_EQ(LiteralList::length(qres.literals), ClauseList::length(qres.premises));
      ASS_EQ(LiteralList::length(qres.literals), ClauseList::length(qres.clausesTheta));

      LiteralList::Iterator literals(qres.literals);
      ClauseList::Iterator premises(qres.premises);
      ClauseList::Iterator clausesTheta(qres.clausesTheta);

      unsigned freshVar = 0;
      while (clausesTheta.hasNext()) {
        freshVar = Int::max(freshVar, clausesTheta.next()->maxVar());
      }
      clausesTheta.reset(qres.clausesTheta);
      freshVar++;

      LiteralList* sideConditions = LiteralList::empty();
      TermList x(freshVar++, false);
      TermList ctx = makeContext(qres.context, qres.term1sort, qres.position, x, qres, &freshVar, sideConditions);
      
      unsigned length = qres.totalLengthClauses() - LiteralList::length(qres.literals) + LiteralList::length(sideConditions) + 2;
      UnitList* ulpremises = UnitList::empty();
      while (premises.hasNext()) {
        UnitList::push(premises.next(), ulpremises);
      }
      Inference* inf = new InferenceMany(Inference::TERM_ALGEBRA_CYCLES, ulpremises);
      Clause* res = new(length) Clause(length,
                                       _premise->inputType(),
                                       inf);

      premises.reset(qres.premises);
      unsigned i = 0;

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
      }
      ASS (!literals.hasNext());
      ASS (!premises.hasNext());
      ASS (!clausesTheta.hasNext());

      LiteralList::Iterator scIt(sideConditions);
      while (scIt.hasNext()) {
        (*res)[i++] = scIt.next();
      }
      (*res)[i++] = Literal::createEquality(false,
                                            x,
                                            ctx,
                                            qres.term1sort);
      (*res)[i++] = Literal::createEquality(true,
                                            x,
                                            qres.term1,
                                            qres.term1sort);

      ASS_EQ(i, length);

      res->setAge(_premise->age() + 1);
      env.statistics->taUniquenessResolution++;
      return res;
    }
    
  private:
    Clause *_premise;
    VirtualIterator<Indexing::ChainQueryResult> _queryResults;
  };

  struct UniquenessGIE::UniquenessGenFn
  {
    UniquenessGenFn(Indexing::ChainIndex* cidx, Clause* premise)
      :
      _cidx(cidx),
      _premise(premise)
    {}
    
    DECL_RETURN_TYPE(VirtualIterator<Clause*>);

    OWN_RETURN_TYPE operator()(Literal* lit)
    {
      CALL("UniquenessGIE::UniquenessGenFn::operator()");

      return vi(new UniquenessGenIterator(_premise, _cidx->queryChains(lit, _premise, true)));
    }
    
  private:
    Indexing::ChainIndex *_cidx;
    Clause* _premise;
  };

  ClauseIterator UniquenessGIE::generateClauses(Clause *c)
  {
    CALL("UniquenessGIE::generateClauses");

    auto it1 = c->getSelectedLiteralIterator();
    auto it2 = getMappingIterator(it1, UniquenessGenFn(_chainIndex, c));
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
              pos = (bool*)ALLOC_KNOWN(c->length() * sizeof(bool), "InfinitenessISE::simplify::pos");
            }
            if (lit->nthArgument(0)->isVar() && (r = deleteLits(c, *lit->nthArgument(0), pos))) {
              goto ret;
            }
            if (lit->nthArgument(1)->isVar() && (r = deleteLits(c, *lit->nthArgument(1), pos))) {
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

  Clause* InfinitenessISE::deleteLits(Kernel::Clause* c, TermList var, bool* positions)
  {
    CALL("InfinitenessISE::deleteLits");
    ASS(var.isVar());

    unsigned toDelete = 0;
    unsigned length = c->length();
    
    for (unsigned i = 0; i < length; i++) {
      Literal *lit = (*c)[i];

      if (lit->isEquality()) {
        TermList *s = lit->nthArgument(0);
        TermList *t = lit->nthArgument(1);
        if (s->isTerm() && s->containsSubterm(var)) {
          return nullptr;
        }
        if (t->isTerm() && t->containsSubterm(var)) {
          return nullptr;
        }
        positions[i] = lit->isPositive() && (TermList::equals(*s, var) || TermList::equals(*t, var));
        toDelete += positions[i];
      } else {
        if (lit->containsSubterm(var)) {
          return nullptr;
        }
        positions[i] = false;
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
      ASS_EQ(i, resLength);
      
      res->setAge(c->age());
      env.statistics->taInfinitenessSimplifications++;
      return res;
    }
  }
 
}
