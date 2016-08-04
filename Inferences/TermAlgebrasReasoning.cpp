/**
 * @file TermAlgebrasReasoning.cpp
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

#include "TermAlgebrasReasoning.hpp"

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
    for (i; (*c)[i] != a; i++) {}
    std::memcpy(res->literals(), c->literals(), length * sizeof(Literal*));
    (*res)[i] = b;

    return res;
  }

  // copy clause c, with the exception of the ith literal
  Clause* removeLit(Clause *c, unsigned i, Inference *inf)
  {
    CALL("removeLit");

    int length = c->length();
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

  // true iff the literal has the form f(x1 ... xn) = f(y1 ... yn)
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

  struct DistinctnessGIE::ConstructorDisequalityIterator
  {
    ConstructorDisequalityIterator(Clause *clause, Literal *lit, bool left, Ordering& ord)
      :
      _clause(clause),
      _lit(lit),
      _freshVar(clause->maxVar() + 1),
      _ord(ord),
      _subst()
    {
      if (left) {
        _l = *lit->nthArgument(0);
        _r = *lit->nthArgument(1);
      } else {
        _l = *lit->nthArgument(1);
        _r = *lit->nthArgument(0);
      }
      _f = _l.isTerm() && termAlgebraConstructor(&_l) ? _l.term()->functor() : 0;
      _sort = SortHelper::getEqualityArgumentSort(_lit);
      _algebra = env.signature->isTermAlgebraSort(_sort) ? env.signature->getTermAlgebraOfSort(_sort) : nullptr;
      if (_algebra) {
        if (_l.isTerm()) {
          _it1 = List<Signature::TermAlgebraConstructor*>::Iterator(_algebra->constructors());
        } else {
          _it1 = List<Signature::TermAlgebraConstructor*>::Iterator(List<Signature::TermAlgebraConstructor*>::empty());
          _it2 = List<Signature::TermAlgebraConstructor*>::Iterator(_algebra->constructors());
        }
      }
      
      // some cases where the rule doesn't apply
      if (!_algebra) {
        _empty = true; // not a term algebra equality
      } else if (_algebra->constructors()->length() <= 1) {
        _empty = true;
      } else if (_l.isTerm() && (!termAlgebraConstructor(&_l) // the LHS is a term with uninterpreted head symbol
                                 || Ordering::isGorGEorE(_ord.compare(_r, _l)))) { // LHS larger than RHS
        _empty = true;
      } else if (_l.isVar() && _r.containsSubterm(_l)) {
        _empty = true;
      } else {
        _empty = false;
      }
    }

    DECL_ELEMENT_TYPE(Clause *);

    bool hasNext() {
      if (_empty) { return false; }

      if (_l.isTerm()) {
        // if the left term has the shape f(s...), iterate over every
        // term algebra constructor that is not f
        if (_it1.hasNext() && _it1.peekAtNext()->functor() == _f) {
          _it1.next();
        }
        return _it1.hasNext();
      } else {
        // if the left term is a variable, iterate over every pair of
        // distinct term algebra constructors
        if (_it1.hasNext() && _it1.peekAtNext()->functor() == _f) {
          _it1.next(); // distinct pairs only
        }
        if (_it1.hasNext()) {
          return true;
        } else {
          while (_it2.hasNext()) {
            _f = _it2.next()->functor();
            unsigned arity = env.signature->getFunction(_f)->arity();
            TermList *args = new TermList [arity];
            for (unsigned i = 0; i < arity; i++) {
              args[i] = TermList(_freshVar++, false);
            }
            TermList fx = TermList(Term::create(_f, arity, args));
            if (!Ordering::isGorGEorE(_ord.compare(fx, _r))) {
              _it1.reset(_algebra->constructors());
              if (_it1.hasNext() && _it1.peekAtNext()->functor() == _f) {
                _it1.next(); // distinct pairs only
              }
              _subst.reset();
              _subst.bind(_l.var(), fx);
              
              ASS(_it1.hasNext());
              return true;
            }
          }
          return false;
        }
      }
    }
    
    OWN_ELEMENT_TYPE next()
    {
      CALL("DistinctnessGIE::ConstructorDisequalityIterator::next()");

      unsigned length = _clause->length();
      Inference *inf = new Inference1(Inference::TERM_ALGEBRA_DISTINCTNESS, _clause);
      Clause *res = new(length) Clause(length,
                                       _clause->inputType(),
                                       inf);
      
      unsigned g = _it1.next()->functor();
      unsigned arity = env.signature->getFunction(g)->arity();
      TermList *args = new TermList [arity];
      for (unsigned i = 0; i < arity; i++) {
        args[i] = TermList(_freshVar++, false);
      }
      Term *term = Term::create(g, arity, args);

      Literal *l = Literal::createEquality(false,
                                           _r,
                                           TermList(term),
                                           _sort);
      
      for (unsigned i = 0; i < length; i++) {
        if ((*_clause)[i] == _lit) {
          (*res)[i] = l;
        } else {
          (*res)[i] = ((*_clause)[i])->apply(_subst);
        }
      }

      res->setAge(_clause->age()+1);
      return res;
    }
  private:
    Ordering& _ord;
    Clause *_clause; // premise l = r \/ A
    Literal *_lit; // selected literal 
    unsigned _f; // the term algebra constructor f, if l is a term algebra with a term algebra symbol
    TermList _l;
    TermList _r;
    unsigned _sort; // sort of the equality (and of the term algebra)
    unsigned _freshVar;
    Signature::TermAlgebra *_algebra;
    List<Signature::TermAlgebraConstructor*>::Iterator _it1;
    List<Signature::TermAlgebraConstructor*>::Iterator _it2;
    bool _empty;
    Substitution _subst;
  };

  struct DistinctnessGIE::ConstructorDisequalityFn
  {
    ConstructorDisequalityFn(Ordering& ord, Clause* clause)
      :
      _clause(clause),
      _ord(ord)
    {}
    DECL_RETURN_TYPE(VirtualIterator<Clause*>);
    OWN_RETURN_TYPE operator()(Literal* lit)
    {
      CALL("DistinctnessGIE::ConstructorDisequalityFn::operator()");

      if (lit->isEquality() && lit->polarity()) {
        return pvi(getConcatenatedIterator(ConstructorDisequalityIterator(_clause,
                                                                          lit,
                                                                          true,
                                                                          _ord),
                                           ConstructorDisequalityIterator(_clause,
                                                                          lit,
                                                                          false,
                                                                          _ord)));
      }
      return pvi(ClauseIterator::getEmpty());
    }
  private:
    Ordering& _ord;
    Clause* _clause;
  };

  ClauseIterator DistinctnessGIE::generateClauses(Clause* c)
  {
    CALL("DistinctnessGIE::generateClauses");

    auto it1 = c->getSelectedLiteralIterator();
    auto it2 = getMappingIterator(it1, ConstructorDisequalityFn(_salg->getOrdering(), c));
    auto it3 = getFlattenedIterator(it2);
    return pvi(it3);
  }

  Clause* DistinctnessISE::simplify(Clause* c)
  {
    CALL("DistinctnessISE::simplify");

    int length = c->length();
    for (int i = length - 1; i >= 0; i--) {
      Literal *lit = (*c)[i];
      if (distinctConstructorsEquality(lit)) {
        if (lit->isPositive()) {
          // equality of the form f(x) = g(y), delete literal from clause
          Clause* res = removeLit(c, i, new Inference1(Inference::TERM_ALGEBRA_DISTINCTNESS, c));
          res->setAge(c->age());
          return res;
        } else {
          // inequality of the form f(x) != g(y) are theory tautologies
          return 0;
        }
      }
    }

    // no equalities between distinct constructors were found
    return c;
  }

  struct InjectivityGIE::ArgumentEqualityIterator
  {
    ArgumentEqualityIterator(Clause *clause, Literal *lit, bool left, Ordering& ord)
      :
      _clause(clause),
      _lit(lit),
      _freshVar(clause->maxVar() + 1),
      _index(0),
      _ord(ord),
      _subst()
    {
      CALL("InjectivityGIE::ArgumentEqualityIterator::ArgumentEqualityIterator");
      
      if (left) {
        _l = *lit->nthArgument(0);
        _r = *lit->nthArgument(1);
      } else {
        _l = *lit->nthArgument(1);
        _r = *lit->nthArgument(0);
      }

      _sort = SortHelper::getEqualityArgumentSort(_lit);
      _algebra = env.signature->isTermAlgebraSort(_sort) ? env.signature->getTermAlgebraOfSort(_sort) : nullptr;
      if (_algebra) {
        if (_l.isVar()) {
          _arity = 0;
          _it = List<Signature::TermAlgebraConstructor*>::Iterator(_algebra->constructors());
        } else {
          _f = _l.term()->functor();
          _type = env.signature->getFunction(_f)->fnType();
          _arity = env.signature->getFunction(_f)->arity();
          TermList *args = new TermList [_arity];
          for (unsigned i = 0; i < _arity; i++) {
            args[i] = TermList(_freshVar + i, false);
          }
          _fy = TermList(Term::create(_f, _arity, args));
        }
      }
      
      // some cases where the rule doesn't apply
      if (!_algebra) {
        _empty = true; // not a term algebra equality
      } else if (_l.isTerm() && (!termAlgebraConstructor(&_l) // the LHS is a term with uninterpreted head symbol
                                 || Ordering::isGorGEorE(_ord.compare(_r, _l)))) { // LHS larger than RHS
        _empty = true;
      } else if (_l.isVar() && _r.containsSubterm(_l)) {
        _empty = true;
      } else {
        _empty = false;
      }
    }
    
    DECL_ELEMENT_TYPE(Clause *);

    bool hasNext() {
      
      if (_empty) { return false; }

      if (_l.isTerm()) {
        // if the left term has the shape f(s1 ... sn), iterate over
        // every argument si
        return _index < _arity;
      } else {
        // if the left term is a variable, iterate over every term
        // algebra constructor and each of their argument
        if (_index < _arity) {
          return true;
        }
        while (_it.hasNext()) {
          _f = _it.next()->functor();
          _arity = env.signature->getFunction(_f)->arity();
          if (_arity > 0) {
            _index = 0;
            _type = env.signature->getFunction(_f)->fnType();
            TermList *args = new TermList [_arity];
            for (unsigned i = 0; i < _arity; i++) {
              args[i] = TermList(_freshVar + i + _arity, false);
            }
            TermList fz = TermList(Term::create(_f, _arity, args));
            if (!Ordering::isGorGEorE(_ord.compare(fz, _r))) {
              for (unsigned i = 0; i < _arity; i++) {
                args[i] = TermList(_freshVar + i, false);
              }
              _fy = TermList(Term::create(_f, _arity, args));
              _subst.reset();
              _subst.bind(_l.var(), fz);
              return true;
            }
          }
        }
        return false;
      }
    }
    
    OWN_ELEMENT_TYPE next()
    {
      CALL("InjectivityGIE::ArgumentEqualityIterator::next()");
      ASS_L(_index, _arity);
      ASS(_algebra);
      ASS_EQ(_arity, env.signature->getFunction(_f)->arity());
      #if VDEBUG
      if (_l.isTerm()) {
        ASS_EQ(_f, _l.term()->functor());
      }
      #endif
      
      Inference *inf = new Inference1(Inference::TERM_ALGEBRA_INJECTIVITY, _clause);
      unsigned length = _clause->length() + 1;
      Clause* res = new(length) Clause(length,
                                       _clause->inputType(),
                                       inf);

      for (unsigned i = 0; i < length - 1; i++) {
        if ((*_clause)[i] == _lit) {
          (*res)[i] = Literal::createEquality(false,
                                              _r,
                                              _fy,
                                              _sort);
        } else {
          (*res)[i] = ((*_clause)[i])->apply(_subst);
        }
      }

      TermList t = _l.isTerm() ? *_l.term()->nthArgument(_index) : TermList(_freshVar + _index + _arity, false);
      (*res)[length - 1] = Literal::createEquality(true,
                                                   t,
                                                   TermList(_freshVar + _index, false),
                                                   _type->arg(_index));
      
      res->setAge(_clause->age() + 1);
      _index++;
      return res;
    }
    
  private:
    Clause *_clause;
    Literal *_lit;
    unsigned _functor;
    TermList _l;
    TermList _r;
    TermList _fy;
    unsigned _index;
    unsigned _arity;
    unsigned _f;
    unsigned _freshVar;
    FunctionType *_type;
    unsigned _sort;
    Signature::TermAlgebra *_algebra;
    List<Signature::TermAlgebraConstructor*>::Iterator _it;
    bool _empty;
    Ordering &_ord;
    Substitution _subst;
  };

  struct InjectivityGIE::ArgumentEqualityFn
  {
    ArgumentEqualityFn(Ordering& ord, Clause* clause)
      :
      _clause(clause),
      _ord(ord)
    {}
    DECL_RETURN_TYPE(VirtualIterator<Clause*>);
    OWN_RETURN_TYPE operator()(Literal* lit)
    {
      CALL("InjectivityGIE::ArgumentEqualityFn::operator()");


      if (lit->isEquality() && lit->polarity()) {
        return pvi(getConcatenatedIterator(ArgumentEqualityIterator(_clause,
                                                                    lit,
                                                                    true,
                                                                    _ord),
                                           ArgumentEqualityIterator(_clause,
                                                                    lit,
                                                                    false,
                                                                    _ord)));
      }
      return pvi(ClauseIterator::getEmpty());
    }
  private:
    Ordering& _ord;
    Clause* _clause;
  };

  ClauseIterator InjectivityGIE::generateClauses(Clause* c)
  {
    CALL("InjectivityGIE::generateClauses");

    auto it1 = c->getSelectedLiteralIterator();
    auto it2 = getMappingIterator(it1, ArgumentEqualityFn(_salg->getOrdering(), c));
    auto it3 = getFlattenedIterator(it2);
    return pvi(it3);
  }

  /*
   * Given a clause f(x1, ..., xn) = f(y1, ... yn) \/ A, this iterator
   * returns the clauses x1 = y1 \/ A up to xn = yn \/ A. For any
   * other literal the iterator is empty
   */
  struct InjectivityGIE1::SubtermIterator
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
      CALL("InjectivityGIE1::SubtermIterator::next()");

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
    FunctionType* _type; // type of f
  };

  struct InjectivityGIE1::SubtermEqualityFn
  {
    SubtermEqualityFn(Clause* premise)
      : _premise(premise) {}
    DECL_RETURN_TYPE(VirtualIterator<Clause*>);
    OWN_RETURN_TYPE operator()(Literal* lit)
    {
      CALL("InjectivityGIE1::SubtermEqualityFn::operator()");

      return pvi(SubtermIterator(_premise, lit));
    }
  private:
    Clause* _premise;
  };

  ClauseIterator InjectivityGIE1::generateClauses(Clause* c)
  {
    CALL("InjectivityGIE1::generateClauses");

    auto it1 = c->getSelectedLiteralIterator();
    auto it2 = getMappingIterator(it1, SubtermEqualityFn(c));
    auto it3 = getFlattenedIterator(it2);
    return pvi(it3);
  }

  Clause* InjectivityISE::simplify(Clause *c)
  {
    CALL("InjectivityISE::simplify");

    int length = c->length();
    for (int i = length - 1; i >= 0; i--) {
      Literal *lit = (*c)[i];
      if (sameConstructorsEquality(lit) && lit->isPositive()) {
        unsigned arity = lit->nthArgument(0)->term()->arity();
        if ((_arityCheck && arity == 1) || arity > 0) {
          FunctionType *type = env.signature->getFunction(lit->nthArgument(0)->term()->functor())->fnType();
          for (unsigned i=0; i < arity; i++) {
            Literal *newlit = Literal::createEquality(true,
                                                      *lit->nthArgument(0)->term()->nthArgument(i),
                                                      *lit->nthArgument(1)->term()->nthArgument(i),
                                                      type->arg(i));
            Clause* res = replaceLit(c, lit, newlit, new Inference1(Inference::TERM_ALGEBRA_INJECTIVITY, c));
            res->setAge(c->age());
            if (i == arity - 1) {
              return res;
            } else {
              // this simplification may result in more than one new
              // clause. All but one are added to unprocessed
              _salg->addNewClause(res);
            }
          }
        }
      }
    }

    // no equalities between similar constructors were found
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

      ASS_EQ(qres->literals->length(), qres->premises->length());
      ASS_EQ(qres->literals->length(), qres->clausesTheta->length());

      List<Literal*>::Iterator literals(qres->literals);
      List<Clause*>::Iterator premises(qres->premises);
      List<Clause*>::Iterator clausesTheta(qres->clausesTheta);
      
      unsigned length = qres->totalLengthClauses() - qres->literals->length();
      UnitList* ulpremises = UnitList::empty();
      while (premises.hasNext()) {
        ulpremises = ulpremises->cons(premises.next());
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

        // create renaming to make sure that variable from different
        // clauses don't end up being confused in the conclusion
        Renaming renaming(maxVar);
        VirtualIterator<unsigned> varIter = p->getVariableIterator();
        while (varIter.hasNext()) {
          unsigned n = renaming.getOrBind(varIter.next());
          maxVar = n > maxVar ? n : maxVar;
        }

        for (unsigned j = 0; j < c->length(); j++) {
          if ((*p)[j] != l) {
            (*res)[i++] = renaming.apply((*c)[j]);
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
 
}
