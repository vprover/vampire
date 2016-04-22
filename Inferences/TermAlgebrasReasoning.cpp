/**
 * @file TermAlgebrasReasoning.cpp
 */

#include "Kernel/Inference.hpp"
#include "Kernel/SortHelper.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Stack.hpp"
#include "Lib/VirtualIterator.hpp"

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

  // true iff the literal has the form f(x1 ... xn) =? g(y1 ... ym)
  // where f and g term algebra constructors. =? stands for either
  // equality of disequality
  bool DistinctnessISE::distinctConstructorsEquality(Literal *lit)
  {
    CALL("DistinctnessISE::distinctConstructorsEquality");

    if (!lit->isEquality())
      return false;

    Signature::Symbol *s = termAlgebraConstructor(lit->nthArgument(0));
    Signature::Symbol *t = termAlgebraConstructor(lit->nthArgument(1));

    return (s && t && s != t);
  }

  Clause* AcyclicityISE::simplify(Clause *c)
  {
    CALL("AcyclicityISE::simplify");

    int length = c->length();
    for (int i = length - 1; i >= 0; i--) {
      Literal *lit = (*c)[i];
      if (cyclicEquality(lit)) {
        if (lit->isPositive()) {
          // cyclic inequality, delete literal from clause
          Clause* res = removeLit(c, i, new Inference1(Inference::TERM_ALGEBRA_ACYCLICITY, c));
          res->setAge(c->age());
          return res;
        } else {
          // cyclic disequality, theory tautologies
          return 0;
        }
      }
    }

    // no cyclic equalities were found
    return c;
  }

  bool AcyclicityISE::cyclicEquality(Literal *lit)
  {
    CALL("AcyclicityISE::cyclicEquality");

    if (!lit->isEquality())
      return false;

    TermList l = *lit->nthArgument(0);
    TermList r = *lit->nthArgument(1);

    bool lcons = l.isTerm() && Lib::env.signature->getFunction(l.term()->functor())->termAlgebraCons();
    bool rcons = r.isTerm() && Lib::env.signature->getFunction(r.term()->functor())->termAlgebraCons();

    if (lcons == rcons) //XOR
      return false;

    if (lcons) {
      return isProperSubterm(r, l);
    } else {
      return isProperSubterm(l, r);
    }
  }

  /*
   * True iff s is a proper subterm of t. t must be a 
   */
  bool AcyclicityISE::isProperSubterm(TermList s, TermList t)
  {
    CALL("AcyclicityISE::isProperSubterm");

    ASS(t.isTerm());

    Stack<TermList> todo(t.term()->arity()); // TermList * sort
    todo.push(t);

    bool notFirst = false;

    while (todo.isNonEmpty()) {
      TermList current = todo.pop();

      //TODO extend the rule to work whenever current unifies with s
      if (notFirst && TermList::equals(current, s))
        return true;

      notFirst = true;

      Signature::Symbol *cons = termAlgebraConstructor(&current);
      // explore only under constructors, not other symbols
      if (cons) {
        Term::Iterator it(current.term());
        while (it.hasNext()) {
          todo.push(it.next());
        }
      }
    }
  
    return false;
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
      if (sameConstructorsEquality(lit)) {
        _type = env.signature->getFunction(lit->nthArgument(0)->term()->functor())->fnType();
        if (lit->polarity()) {
          _length = lit->nthArgument(0)->term()->arity();
        } else {
          _length = 1;
        }
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
      
      if (_lit->polarity()) {
        // from the clause f(x1 ... xn) = f(y1 .. yn) \/ C, we create
        // a new clause xi = yi \/ C. In this case, next() can be
        // called n times to create the n relevant conclusions.
        Literal *l = Literal::createEquality(true,
                                             *_lit->nthArgument(0)->term()->nthArgument(_index),
                                             *_lit->nthArgument(1)->term()->nthArgument(_index),
                                             _type->arg(_index));
      
        res = replaceLit(_clause, _lit, l, inf);
      } else {
        // in the created clause, we replace the literal _lit (which
        // has the shape f(x1 ... xn) != f(y1 .. yn)) by n new
        // disequalities xi != yi. The rest of the original clause
        // remains identical. In this case, next() can be called only
        // one time since there is only one conclusion.
        unsigned nlits = _lit->nthArgument(0)->term()->arity();
        int clength = _clause->length() - 1 + nlits;
        res = new(clength) Clause(clength, _clause->inputType(), inf);

        unsigned i = 0;
        for (i; (*_clause)[i] != _lit; i++) {}
        std::memcpy(res->literals(), _clause->literals(), i * sizeof(Literal*));
        for (unsigned j = 0; j < nlits; j++) {
          (*res)[i + j] = Literal::createEquality(false,
                                                  *_lit->nthArgument(0)->term()->nthArgument(j),
                                                  *_lit->nthArgument(1)->term()->nthArgument(j),
                                                  _type->arg(j));
        }
        std::memcpy(res->literals() + i + nlits, _clause->literals() + i + 1, (clength - i - nlits) * sizeof(Literal*));
      }
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

  // true iff the literal has the form f(x1 ... xn) = f(y1 ... yn)
  // where f is a term algebra constructor
  bool InjectivityGIE::sameConstructorsEquality(Literal *lit)
  {
    CALL("InjectivityGIE::sameConstructorsEquality");

    if (!lit->isEquality())
      return false;

    Signature::Symbol *s = termAlgebraConstructor(lit->nthArgument(0));
    Signature::Symbol *t = termAlgebraConstructor(lit->nthArgument(1));

    return (s && s == t);
  }

  /*
   * Given a clause f(s) = t \/ A, this iterator returns the clauses
   * s1 != t \/ A up to sn != t \/ A where s1 ... sn are all the
   * proper subterms of f(s) of the same sort as t. The constructor
   * symbol f can be on either side of the equality, but if both sides
   * have a constructor as top-level, nothing is returned as either
   * injectivity or distinctness should be applied first. This
   * shouldn't compromise soundness (to be verified). For any other
   * literal the iterator is empty
   */
  /*
  struct AcyclicityGIE::DeepSubtermIterator
  {
    DeepSubtermIterator(Clause *clause, Literal *lit)
      : _lit(lit),
        _clause(clause)
    {
      if (oneConstructorPositiveEquality(lit, _fs, _t)) {
        _sort = env.signature->getFunction(lit->nthArgument(0)->term()->functor())->fnType()->result();
        _subterms = properSubterms(_fs, _sort);
      } else {
        _subterms = List<TermList>::empty();
      }
    }

    DECL_ELEMENT_TYPE(Clause *);

    bool hasNext() { return List<TermList>::isNonEmpty(_subterms); }
    OWN_ELEMENT_TYPE next()
    {
      CALL("AcyclicityGIE::DeepSubtermIterator::next()");
      Literal *l = Literal::createEquality(false,
                                           _subterms->head(),
                                           _t,
                                           _sort);
      List<TermList>* old = _subterms;
      _subterms = _subterms->tail();
      delete old;

      Clause *res = replaceLit(_clause,
                               _lit,
                               l,
                               new Inference1(Inference::TERM_ALGEBRA_ACYCLICITY, _clause));
      res->setAge(_clause->age()+1);
      return res;
    }
  private:
    Literal* _lit;
    Clause* _clause;
    FunctionType* _type;
    List<TermList>* _subterms;
    unsigned _sort;
    TermList _fs, _t;
  };

  struct AcyclicityGIE::SubtermInequalityFn
  {
    SubtermInequalityFn(Clause* premise)
      : _premise(premise) {}
    DECL_RETURN_TYPE(VirtualIterator<Clause*>);
    OWN_RETURN_TYPE operator()(Literal* lit)
    {
      CALL("AcyclicityGIE::SubtermInequalityFn::operator()");

      return pvi(DeepSubtermIterator(_premise, lit));
    }
  private:
    Clause* _premise;
  };

  ClauseIterator AcyclicityGIE::generateClauses(Clause* c)
  {
    CALL("AcyclicityGIE::generateClauses");

    auto it1 = c->getSelectedLiteralIterator();
    auto it2 = getMappingIterator(it1, SubtermInequalityFn(c));
    auto it3 = getFlattenedIterator(it2);
    return pvi(it3);
  }

  List<TermList>* AcyclicityGIE::properSubterms(TermList t, unsigned sort)
  {
    CALL("AcyclicityGIE::properSubterms");
    ASS(t.isTerm());

    List<TermList>* res = List<TermList>::empty();
    Stack<pair<TermList, unsigned>> todo(t.term()->arity()); // TermList * sort
    todo.push(make_pair(t, 0u)); // mark the sort as 0 just as a cheap
                                // way to ensure that t is not cons'd
                                // to the result

    while (todo.isNonEmpty()) {
      pair<TermList, unsigned> current = todo.pop();

      Signature::Symbol *cons = termAlgebraConstructor(&current.first);
      // explore only under constructors, not other symbols
      if (cons) {
        Term::Iterator it(current.first.term());
        while (it.hasNext()) {
          TermList next = it.next();
          unsigned nextSort;
          if (next.isTerm()) {
            nextSort = SortHelper::getResultSort(next.term());
          } else {
            ASS(next.isVar());
            nextSort = SortHelper::getVariableSort(next, current.first.term());
          }
          todo.push(make_pair(next, nextSort));
        }
      }

      if (current.second == sort) {
        res = res->cons(current.first);
      }
    }
  
    return res;
  }

  bool AcyclicityGIE::oneConstructorPositiveEquality(Literal *lit, TermList &fs, TermList &t)
  {
    CALL("AcyclicityGIE::oneConstructorPositiveEquality");

    if (!lit->isEquality() || !lit->polarity())
      return false;

    TermList l = *lit->nthArgument(0);
    TermList r = *lit->nthArgument(1);

    bool lcons = l.isTerm() && Lib::env.signature->getFunction(l.term()->functor())->termAlgebraCons();
    bool rcons = r.isTerm() && Lib::env.signature->getFunction(r.term()->functor())->termAlgebraCons();

    if (lcons == rcons) //XOR
      return false;

    if (lcons) {
      fs = l;
      t = r;
    } else {
      fs = r;
      t = r;
    }
    return true;
  }
  */
  
}
