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

    int length = c->length();
    for (int i = length - 1; i >= 0; i--) {
      Literal *lit = (*c)[i];
      if (sameConstructorsEquality(lit) && lit->isPositive()) {
        if (lit->nthArgument(0)->term()->arity() == 1) {
          FunctionType *type = env.signature->getFunction(lit->nthArgument(0)->term()->functor())->fnType();
          Literal *newlit = Literal::createEquality(true,
                                                    *lit->nthArgument(0)->term()->nthArgument(0),
                                                    *lit->nthArgument(1)->term()->nthArgument(0),
                                                    type->arg(0));
          Clause* res = replaceLit(c, lit, newlit, new Inference1(Inference::TERM_ALGEBRA_INJECTIVITY, c));
          res->setAge(c->age());
          return res;
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
        /*Renaming renaming(maxVar);
        VirtualIterator<unsigned> varIter = p->getVariableIterator();
        while (varIter.hasNext()) {
          unsigned n = renaming.getOrBind(varIter.next());
          maxVar = n > maxVar ? n : maxVar;
          }*/

        for (unsigned j = 0; j < c->length(); j++) {
          if ((*p)[j] != l) {
            (*res)[i++] = (*c)[j]; //renaming.apply((*c)[j]);
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
