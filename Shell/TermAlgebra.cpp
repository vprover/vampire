#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Stack.hpp"

#include "TermAlgebra.hpp"

using namespace Kernel;
using namespace Lib;

namespace Shell {

TermAlgebraConstructor::TermAlgebraConstructor(vstring name,
                                               unsigned rangeSort,
                                               unsigned arity,
                                               const vstring *destructorNames,
                                               const unsigned *argSorts) :
  _cname(name),
  _rangeSort(rangeSort),
  _arity(arity),
  _destructorNames(arity),
  _argSorts(arity),
  _destructorFunctors(arity)
{
  for (unsigned i = 0; i < _arity; i++) {
    _destructorNames[i] = destructorNames[i];
    _argSorts[i] = argSorts[i];
  }
}

bool TermAlgebraConstructor::recursive()
{
  CALL("TermAlgebraConstructor::recursive");
  
  for (unsigned i=0; i < _arity; i++) {
    if (_argSorts[i] == _rangeSort) {
      // this constructor has a recursive argument
      return true;
    }
  }
  return false;
}

void TermAlgebraConstructor::createSymbols()
{
  CALL("TermAlgebraConstructors::createSymbols");

  bool added;
  BaseType *type;
  _functor = env.signature->addFunction(_cname, _arity, added);
  ASS(added);
  type = new FunctionType(_arity, _argSorts.begin(), _rangeSort);
  env.signature->getFunction(_functor)->setType(type);
  env.signature->getFunction(_functor)->markTermAlgebraCons();

  // destructors
  for (unsigned i = 0; i < _arity; i++) {
    _destructorFunctors[i] = env.signature->addFunction(_destructorNames[i], 1, added);
    ASS(added);
    type = new FunctionType(1, &_rangeSort, _argSorts[i]);
    env.signature->getFunction(_destructorFunctors[i])->setType(type);
  }
}

bool TermAlgebraConstructor::addSubtermDefinitions(unsigned subtermPredicate, UnitList*& units)
{
  CALL("TermAlgebraConstructor::addSubtermDefinitions");

  Formula::VarList *v = Formula::VarList::empty();
  Formula::SortList *s = Formula::SortList::empty();
  Stack<TermList> args;
  bool hasRecursiveArg = false;
  unsigned varNum = 0;
  
  for (unsigned i=0; i < _arity; i++) {
    if (_argSorts[i] == _rangeSort) {
      hasRecursiveArg = true;
    }
    TermList x(varNum++, false);
    args.push(x);
    Formula::VarList::push(x.var(), v);
    Formula::SortList::push(_argSorts[i], s);
  }
  if (!hasRecursiveArg) {
    return false;
  }

  TermList right(Term::create(_functor, args.size(), args.begin()));
  TermList z(varNum++, false);
  Formula::VarList *v2 = v->cons(z.var());
  Formula::SortList *s2 = s->cons(_rangeSort);
  varNum = 0;

  for (unsigned i=0; i < _arity; i++) {
    if (_argSorts[i] == _rangeSort) {
      TermList y(varNum, false);
      // Direct subterms are subterms: Sub(y, c(x1, ... y ..., xn))
      Formula *def = new QuantifiedFormula(Connective::FORALL,
                                           v,
                                           s,
                                           new AtomicFormula(Literal::create2(subtermPredicate, true, y, right)));
      UnitList::push(new FormulaUnit(def,
                                     new Inference(Inference::TERM_ALGEBRA_ACYCLICITY),
                                     Unit::AXIOM),
                     units);
      // Transitivity of the subterm relation: Sub(z, y) -> Sub(z, c(x1, ... y , xn))
      Formula *trans = new QuantifiedFormula(Connective::FORALL,
                                             v2,
                                             s2,
                                             new BinaryFormula(Connective::IMP,
                                                               new AtomicFormula(Literal::create2(subtermPredicate, true, z, y)),
                                                               new AtomicFormula(Literal::create2(subtermPredicate, true, z, right))));
      UnitList::push(new FormulaUnit(trans,
                                     new Inference(Inference::TERM_ALGEBRA_ACYCLICITY),
                                     Unit::AXIOM),
                     units);
    }
    varNum++;
  }
  return true;
}

TermAlgebra::TermAlgebra(vstring name,
                         unsigned sort,
                         unsigned n,
                         TermAlgebraConstructor** constrs,
                         bool allowsCyclicTerms) :
  _tname(name),
  _n(n),
  _constrs(n),
  _sort(sort),
  _allowsCyclicTerms(allowsCyclicTerms)
{
  for (unsigned i = 0; i < n; i++) {
    ASS(constrs[i]->rangeSort() == _sort);
    _constrs[i] = constrs[i];
  }
}

bool TermAlgebra::emptyDomain()
{
  CALL("TermAlgebra::emptyDomain");

  if (_n == 0) {
    return true;
  }

  if (_allowsCyclicTerms) {
    return false;
  }

  for (unsigned i = 0; i < _n; i++) {
    if (!(_constrs[i]->recursive())) {
      return false;
    }
  }
  return true;
}

unsigned TermAlgebra::getSubtermPredicate() {
  CALL("TermAlgebra::getSubtermPredicate");

  bool added;
  unsigned s = env.signature->addPredicate(getSubtermPredicateName(), 2, added);

  if (added) {
    // declare a binary predicate subterm
    Stack<unsigned> args;
    args.push(_sort); args.push(_sort);
    env.signature->getPredicate(s)->setType(new PredicateType(args.size(),args.begin()));
  }

  return s;
}

void TermAlgebra::addExhaustivenessAxiom(UnitList*& units)
{
  CALL("TermAlgebra::addExhaustivenessAxiom");

  TermList x(0, false);
  Stack<TermList> argTerms;

  FormulaList *l = FormulaList::empty();

  for (unsigned i = 0; i < _n ; i++) {
    TermAlgebraConstructor *c = _constrs[i];
    argTerms.reset();
    
    for (unsigned j = 0; j < c->arity(); j++) {
      TermList t(Term::create1(c->destructorFunctor(j), x));
      argTerms.push(t);
    }
    
    TermList rhs(Term::create(c->functor(),
                              argTerms.size(),
                              argTerms.begin()));
    FormulaList::push(new AtomicFormula(Literal::createEquality(true, x, rhs, _sort)),
                      l);
  }

  Formula::VarList* vars = Formula::VarList::empty()->cons(x.var());
  Formula::SortList* sorts = Formula::SortList::empty()->cons(_sort);

  Formula *axiom;
  switch (l->length()) {
  case 0:
    // the algebra cannot have 0 constructors
    ASSERTION_VIOLATION;
  case 1:
    axiom = new QuantifiedFormula(Connective::FORALL, vars, sorts, l->head());
    break;
  default:
    axiom = new QuantifiedFormula(Connective::FORALL,
                                  vars,
                                  sorts,
                                  new JunctionFormula(Connective::OR, l));
  }

  UnitList::push(new FormulaUnit(axiom,
                                 new Inference(Inference::TERM_ALGEBRA_EXHAUSTIVENESS),
                                 Unit::AXIOM),
                 units);
}

void TermAlgebra::addDistinctnessAxiom(UnitList*& units)
{
  CALL("TermAlgebra::addDistinctnessAxiom");

  unsigned varnum = 0;
  Formula::VarList *vars1, *vars2;
  Formula::SortList *sorts1, *sorts2 = Formula::SortList::empty();

  Stack<TermList> argTerms;

  for (unsigned i = 0; i < _n; i++) {
    TermAlgebraConstructor* c = _constrs[i];

    // build LHS
    vars1 = Formula::VarList::empty();
    sorts1 = Formula::SortList::empty();
    argTerms.reset();
    
    for (unsigned j = 0; j < c->arity(); j++) {
      TermList var(varnum++, false);
      argTerms.push(var);
      Formula::VarList::push(var.var(), vars1);
      Formula::SortList::push(c->argSort(j), sorts1);
    }
    
    TermList lhs(Term::create(c->functor(),
                              argTerms.size(),
                              argTerms.begin()));
    
    for (unsigned k = i + 1; k < _n; k++) {
      c = _constrs[k];

      // build RHS
      vars2 = vars1;
      sorts2 = sorts1;
      argTerms.reset();
      
      for (unsigned j = 0; j < c->arity(); j++) {
        TermList var(varnum++, false);
        argTerms.push(var);
        Formula::VarList::push(var.var(), vars2);
        Formula::SortList::push(c->argSort(j), sorts2);
      }
      TermList rhs(Term::create(c->functor(),
                                argTerms.size(),
                                argTerms.begin()));

      Formula *eq = new AtomicFormula(Literal::createEquality(false,
                                                              lhs,
                                                              rhs,
                                                              _sort));
      Formula* axiom = Formula::VarList::isEmpty(vars2) ? eq : new QuantifiedFormula(Connective::FORALL,
                                                                                     vars2,
                                                                                     sorts2,
                                                                                     eq);
      
      UnitList::push(new FormulaUnit(axiom,
                                     new Inference(Inference::TERM_ALGEBRA_DISTINCTNESS),
                                     Unit::AXIOM),
                     units);
    }
  }
}

void TermAlgebra::addInjectivityAxiom(UnitList*& units)
{
  CALL("TermAlgebra::addInjectivityAxiom");

  Stack<TermList> argTermsX;
  Stack<TermList> argTermsY;
  
  for (unsigned i = 0; i < _n; i++) {
    TermAlgebraConstructor* c = _constrs[i];
    
    if (c->arity() != 0) {
      FormulaList *implied = FormulaList::empty();
      Formula::VarList* vars = Formula::VarList::empty();
      Formula::SortList* sorts = Formula::SortList::empty();

      argTermsX.reset();
      argTermsY.reset();
      
      for (unsigned j = 0; j < c->arity(); j++) {
        TermList x(j * 2, false);
        TermList y(j * 2 + 1, false);
        sorts = sorts->cons(c->argSort(j))->cons(c->argSort(j));
        vars = vars->cons(x.var())->cons(y.var());
        argTermsX.push(x);
        argTermsY.push(y);
        FormulaList::push(new AtomicFormula(Literal::createEquality(true, x, y, c->argSort(j))),
                          implied);
      }

      TermList lhs(Term::create(c->functor(),
                                argTermsX.size(),
                                argTermsX.begin()));
      TermList rhs(Term::create(c->functor(),
                                argTermsY.size(),
                                argTermsY.begin()));
      Formula *eql = new AtomicFormula(Literal::createEquality(true, lhs, rhs, _sort));

      for (unsigned j = 0; j < c->arity(); j++) {
        TermList x(j * 2, false);
        TermList y(j * 2 + 1, false);
        Formula *eqr = new AtomicFormula(Literal::createEquality(true, x, y, c->argSort(j)));

        Formula *axiom = new QuantifiedFormula(Connective::FORALL,
                                               vars,
                                               sorts,
                                               new BinaryFormula (Connective::IMP, eql, eqr));
        UnitList::push(new FormulaUnit(axiom,
                                       new Inference(Inference::TERM_ALGEBRA_INJECTIVITY),
                                       Unit::AXIOM),
                       units);
      }
    }
  }
}
  
void TermAlgebra::addAcyclicityAxiom(UnitList*& units)
{
  CALL("TermAlgebra::addAcyclicityAxiom");

  unsigned pred = getSubtermPredicate();

  if (!_allowsCyclicTerms) {
    bool rec = false;
  
    for (unsigned i = 0; i < _n; i++) {
      if (_constrs[i]->addSubtermDefinitions(pred, units)) {
        rec = true;
      }
    }
  
    if (rec) {
      // rec <=> the subterm relation is non-empty

      TermList x(0, false);

      // add acyclicity axiom: ~Sub(x,x)
      Formula *acycl = new QuantifiedFormula(Connective::FORALL,
                                             Formula::VarList::empty()->cons(x.var()),
                                             Formula::SortList::empty()->cons(_sort),
                                             new AtomicFormula(Literal::create2(pred, false, x, x)));
      UnitList::push(new FormulaUnit(acycl,
                                     new Inference(Inference::TERM_ALGEBRA_ACYCLICITY),
                                     Unit::AXIOM),
                     units);
    }
  }
}

}
