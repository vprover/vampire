/**
 * @file TermAlgebrasReasoning.cpp
 */

#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/SortHelper.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Stack.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Statistics.hpp"

#include "TermAlgebrasReasoning.hpp"

#include <cstring>

using namespace Kernel;

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
      Signature::Symbol *s = Lib::env.signature->getFunction(t->term()->functor());

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
    ConstructorDisequalityIterator(Clause *clause, Literal *lit, unsigned f, TermList t)
      :
      _clause(clause),
      _lit(lit),
      _functor(f),
      _t(t),
      _sort(env.signature->getFunction(f)->fnType()->result()),
      _freshVar(clause->maxVar() + 1),
      _it(env.signature->getTermAlgebraOfSort(_sort)->constructors())
    {}

    DECL_ELEMENT_TYPE(Clause *);

    bool hasNext() {
      if (_it.hasNext() && _it.peekAtNext()->functor() == _functor) {
        _it.next();
      }
      return _it.hasNext();
    }
    
    OWN_ELEMENT_TYPE next()
    {
      CALL("DistinctnessGIE::ConstructorDisequalityIterator::next()");

      Clause *res;
      Inference *inf = new Inference1(Inference::TERM_ALGEBRA_DISTINCTNESS, _clause);

      unsigned g = _it.next()->functor();
      unsigned arity = env.signature->getFunction(g)->arity();
      TermList *args = new TermList [arity];
      for (unsigned i = 0; i < arity; i++) {
        args[i] = TermList(_freshVar + i, false);
      }
      Term *term = Term::create(g, arity, args);
      
      Literal *l = Literal::createEquality(false,
                                           _t,
                                           TermList(term),
                                           _sort);
      
      res = replaceLit(_clause, _lit, l, inf);
      res->setAge(_clause->age()+1);
      return res;
    }
  private:
    Clause *_clause;
    Literal *_lit;
    unsigned _functor;
    TermList _t;
    unsigned _sort;
    unsigned _freshVar;
    Signature::TermAlgebra *_algebra;
    List<Signature::TermAlgebraConstructor*>::Iterator _it;
  };

  struct DistinctnessGIE::ConstructorDisequalityFn
  {
    ConstructorDisequalityFn(Ordering& ord, Clause* premise)
      :
      _premise(premise),
      _ord(ord)  
    {}
    DECL_RETURN_TYPE(VirtualIterator<Clause*>);
    OWN_RETURN_TYPE operator()(Literal* lit)
    {
      CALL("DistinctnessGIE::ConstructorDisequalityFn::operator()");

      if (lit->isEquality() && lit->polarity()) {
        Kernel::Ordering::Result cmp = _ord.compare(*lit->nthArgument(0), *lit->nthArgument(1));
        Signature::Symbol *s = termAlgebraConstructor(lit->nthArgument(0));
        Signature::Symbol *t = termAlgebraConstructor(lit->nthArgument(1));
        
        if (s && !t) {
          if (cmp == Kernel::Ordering::INCOMPARABLE
              || cmp == Kernel::Ordering::GREATER
              || cmp == Kernel::Ordering::GREATER_EQ) {
            return pvi(ConstructorDisequalityIterator(_premise,
                                                      lit,
                                                      lit->nthArgument(0)->term()->functor(),
                                                      *lit->nthArgument(1)));
          }
        } else if (!s && t) {
          if (cmp == Kernel::Ordering::INCOMPARABLE
              || cmp == Kernel::Ordering::LESS
              || cmp == Kernel::Ordering::LESS_EQ) {
            return pvi(ConstructorDisequalityIterator(_premise,
                                                      lit,
                                                      lit->nthArgument(1)->term()->functor(),
                                                      *lit->nthArgument(0)));
          }
        }
      }
      return pvi(ClauseIterator::getEmpty());
    }
  private:
    Ordering& _ord;
    Clause* _premise;
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
    ArgumentEqualityIterator(Clause *clause, Literal *lit, TermList fs, TermList t)
      :
      _clause(clause),
      _fs(fs),
      _freshVar(clause->maxVar() + 1),
      _type(env.signature->getFunction(fs.term()->functor())->fnType()),
      _index(0),
      _arity(fs.term()->arity()),
      _length(clause->length() + 1)
    {
      ASS(fs.isTerm());

      unsigned length = clause->length();
      _lits = new Literal*[length];

      TermList *args = new TermList[_arity];
      for (unsigned i = 0; i < _arity; i++) {
        args[i] = TermList(_freshVar + i, false);
      }
      Term *term = Term::create(fs.term()->functor(), _arity, args);
      
      unsigned i = 0;
      for (i; (*clause)[i] != lit; i++) {}
      std::memcpy(_lits, clause->literals(), length * sizeof(Literal*));
      
      _lits[i] = Literal::createEquality(false,
                                         t,
                                         TermList(term),
                                         _type->result());
    }

    DECL_ELEMENT_TYPE(Clause *);

    bool hasNext() {
      return _index < _arity;
    }
    
    OWN_ELEMENT_TYPE next()
    {
      CALL("InjectivityGIE::ArgumentEqualityIterator::next()");
      Inference *inf = new Inference1(Inference::TERM_ALGEBRA_INJECTIVITY, _clause);
      Clause* res = new(_length) Clause(_length,
                                        _clause->inputType(),
                                        inf);

      std::memcpy(res->literals(), _lits, (_length - 1) * sizeof(Literal*));
      
      (*res)[_length - 1] = Literal::createEquality(true,
                                                    *_fs.term()->nthArgument(_index),
                                                    TermList(_freshVar + _index, false),
                                                    _type->arg(_index));
      
      res->setAge(_clause->age() + 1);
      _index++;
      return res;
    }
  private:
    Clause *_clause;
    Literal **_lits;
    unsigned _functor;
    TermList _fs;
    unsigned _index;
    unsigned _arity;
    unsigned _freshVar;
    FunctionType *_type;
    unsigned _length;
  };

  struct InjectivityGIE::ArgumentEqualityFn
  {
    ArgumentEqualityFn(Ordering& ord, Clause* premise)
      :
      _premise(premise),
      _ord(ord)  
    {}
    DECL_RETURN_TYPE(VirtualIterator<Clause*>);
    OWN_RETURN_TYPE operator()(Literal* lit)
    {
      CALL("InjectivityGIE::ArgumentEqualityFn::operator()");

      if (lit->isEquality() && lit->polarity()) {
        Kernel::Ordering::Result cmp = _ord.compare(*lit->nthArgument(0), *lit->nthArgument(1));
        Signature::Symbol *s = termAlgebraConstructor(lit->nthArgument(0));
        Signature::Symbol *t = termAlgebraConstructor(lit->nthArgument(1));
        
        if (s && !t) {
          if (cmp == Kernel::Ordering::INCOMPARABLE
              || cmp == Kernel::Ordering::GREATER
              || cmp == Kernel::Ordering::GREATER_EQ) {
            return pvi(ArgumentEqualityIterator(_premise,
                                                lit,
                                                *lit->nthArgument(0),
                                                *lit->nthArgument(1)));
          }
        } else if (!s && t) {
          if (cmp == Kernel::Ordering::INCOMPARABLE
              || cmp == Kernel::Ordering::LESS
              || cmp == Kernel::Ordering::LESS_EQ) {
            return pvi(ArgumentEqualityIterator(_premise,
                                                lit,
                                                *lit->nthArgument(1),
                                                *lit->nthArgument(0)));
          }
        }
      }
      return pvi(ClauseIterator::getEmpty());
    }
  private:
    Ordering& _ord;
    Clause* _premise;
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
        if (arity > 0) {
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
 
}
