
/*
 * File TermAlgebra.cpp.
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
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"

#include "Lib/Stack.hpp"

using namespace Kernel;
using namespace Lib;

namespace Shell {

vstring TermAlgebraConstructor::name()
{
  return env.signature->functionName(_functor);
}

TermAlgebraConstructor::TermAlgebraConstructor(unsigned functor, Array<unsigned> destructors)
  : _functor(functor),
    _hasDiscriminator(false),
    _destructors(destructors)
{
  _type = env.signature->getFunction(_functor)->fnType();
  ASS_REP(env.signature->getFunction(_functor)->termAlgebraCons(),
          env.signature->functionName(_functor));
  ASS_EQ(_type->arity(), destructors.size());
}

TermAlgebraConstructor::TermAlgebraConstructor(unsigned functor, unsigned discriminator, Array<unsigned> destructors)
  : _functor(functor),
    _hasDiscriminator(true),
    _discriminator(discriminator),
    _destructors(destructors)
{
  _type = env.signature->getFunction(_functor)->fnType();
  ASS_REP(env.signature->getFunction(_functor)->termAlgebraCons(),
          env.signature->functionName(_functor));
  ASS_EQ(_type->arity(), destructors.size());
}

bool TermAlgebraConstructor::recursive()
{
  CALL("TermAlgebraConstructor::recursive");

  for (unsigned i=0; i < arity(); i++) {
    if (_type->arg(i) == _type->result()) {
      // this constructor has a recursive argument
      return true;
    }
  }
  return false;
}

vstring TermAlgebraConstructor::discriminatorName()
{
  CALL("TermAlgebraConstructor::discriminatorName");

  return "$is_" + name();
}

vstring TermAlgebraConstructor::getCtxFunctionName(TermAlgebra* ta) {
  return "$ctx_" + name() + "_" + ta->name();
}

unsigned TermAlgebraConstructor::getCtxFunction(TermAlgebra* ta) {
  CALL("TermAlgebra::getCtxFunction");

  bool added;
  unsigned s = env.signature->addFunction(getCtxFunctionName(ta), arity(), added);  
  
  if (added) {
    Stack<unsigned> argSorts;
    for (unsigned i; i < arity(); i++) {
      if (!env.signature->isTermAlgebraSort(argSort(i))) {
        argSorts.push(argSort(i));
      } else {
        TermAlgebra* tai = env.signature->getTermAlgebraOfSort(argSort(i));
        if (tai->isMutualType(ta)) {
          argSorts.push(tai->contextSort(ta));
        } else {
          argSorts.push(argSort(i));
        }        
      }      
    }
    ASS_EQ(argSorts.size(), arity());
    unsigned resultSort = env.signature->getTermAlgebraOfSort(rangeSort())->contextSort(ta);
    env.signature->getFunction(s)->setType(OperatorType::getFunctionType(arity(),
                                                                         argSorts.begin(),
                                                                         resultSort));
  }

  return s;
}

TermAlgebra::TermAlgebra(unsigned sort,
                         vstring name,
                         unsigned n,
                         TermAlgebraConstructor** constrs,
                         bool allowsCyclicTerms) :
  _sort(sort),
  _name(name),
  _mutualTypes(nullptr),
  _contextSorts(),
  _n(n),
  _allowsCyclicTerms(allowsCyclicTerms),
  _constrs(n),
  _domain(DomainSize::NOT_COMPUTED)
{
  for (unsigned i = 0; i < n; i++) {
    ASS(constrs[i]->rangeSort() == _sort);
    _constrs[i] = constrs[i];
  }
}

void TermAlgebra::computeDomainSize() {
  CALL("TermAlgebra::computeDomainSize");
  ASS_EQ(_domain, DomainSize::NOT_COMPUTED);

  _domain = DomainSize::EMPTY;
  if (_n == 0) {
    return;
  }

  if (_allowsCyclicTerms
      && _n == 1
      && _constrs[0]->recursive()
      && _constrs[0]->arity() == 1) {
    _domain = DomainSize::SINGLETON_CDT;
    return;
  }

  // for recursively defined types (possibly mutual), must check that
  // there exists a smallest element
  if (isMutualType(this)) {
    if (_allowsCyclicTerms) {
      _domain = DomainSize::INFINITE;
    } else {
      VirtualIterator<TermAlgebra*> it = mutualTypes();
      while (it.hasNext()) {
        if (it.next()->existsSmallestTerm()) {
          _domain = DomainSize::INFINITE;
          return;
        }
      }
      _domain = DomainSize::EMPTY;
    }
    return;
  }

  for (unsigned i = 0; i < _n; i++) {
    if (_constrs[i]->arity() > 0) {
      _domain = DomainSize::UNKNOWN;
      return;
    }
  }
  _domain = DomainSize::FINITE;
}

bool TermAlgebra::existsSmallestTerm() {
  CALL("TermAlgebra::existsSmallestTerm");

  for (unsigned i = 0; i < _n; i++) {
    TermAlgebraConstructor* c = _constrs[i];
    unsigned j;
    for (j = 0; j < c->arity(); j++) {
      unsigned s = c->argSort(j);
      if (isMutualTypeSort(s)) {
        break;
      }
    }
    if (j == c->arity()) {
      return true;
    }
  }
  return false;
}

bool TermAlgebra::emptyDomain()
{
  CALL("TermAlgebra::emptyDomain");

  if (_domain == DomainSize::NOT_COMPUTED) {
    computeDomainSize();
  }

  return _domain == DomainSize::EMPTY;
}

bool TermAlgebra::singletonCodatatype()
{
  CALL("TermAlgebra::singletonCodatatype");

  if (_domain == DomainSize::NOT_COMPUTED) {
    computeDomainSize();
  }

  return _domain == DomainSize::SINGLETON_CDT;
}

bool TermAlgebra::finiteDomain()
{
  CALL("TermAlgebra::finiteDomain");

  if (_domain == DomainSize::NOT_COMPUTED) {
    computeDomainSize();
  }

  return (_domain == DomainSize::FINITE || _domain == DomainSize::SINGLETON_CDT);
}

bool TermAlgebra::infiniteDomain()
{
  CALL("TermAlgebra::infiniteDomain");

  if (_domain == DomainSize::NOT_COMPUTED) {
    computeDomainSize();
  }

  return _domain == DomainSize::INFINITE;
}

bool TermAlgebra::isMutualType(TermAlgebra *ta)
{
  CALL("TermAlgebra::isMutualType");

  return isMutualTypeSort(ta->sort());
}

bool TermAlgebra::isMutualTypeSort(unsigned tasort)
{
  CALL("TermAlgebra::isMutualType");

  if (!_mutualTypes) {
    setMutualTypes();
  }

  return _mutualTypes->contains(tasort);
}

struct TermAlgebraOfSortFn
{
  DECL_RETURN_TYPE(TermAlgebra*);

  OWN_RETURN_TYPE operator()(unsigned sort)
  {
    return env.signature->getTermAlgebraOfSort(sort);
  }
};

VirtualIterator<TermAlgebra*> TermAlgebra::mutualTypes()
{
  CALL("TermAlgebra::mutualTypes");

  if (!_mutualTypes) {
    setMutualTypes();
  }

  Set<unsigned>::Iterator it(*_mutualTypes);
  auto it2 = getMappingIterator(it, TermAlgebraOfSortFn());
  return pvi(it2);
}

VirtualIterator<unsigned> TermAlgebra::mutualTypesSorts()
{
  CALL("TermAlgebra::mutualTypesSorts");

  if (!_mutualTypes) {
    setMutualTypes();
  }

  return pvi(Set<unsigned>::Iterator(*_mutualTypes));
}
  
vstring TermAlgebra::getSubtermPredicateName(TermAlgebra* ta) {
  return "$subterm_" + ta->name() + "_" + name();
}

unsigned TermAlgebra::getSubtermPredicate(TermAlgebra* ta) {
  CALL("TermAlgebra::getSubtermPredicate");

  bool added;
  unsigned s = env.signature->addPredicate(getSubtermPredicateName(ta), 2, added);

  if (added) {
    // declare a binary predicate subterm
    env.signature->getPredicate(s)->setType(OperatorType::getPredicateType({ta->sort(), _sort}));
  }

  return s;
}

unsigned TermAlgebra::contextSort(TermAlgebra* ta) {
  if (_contextSorts.find(ta)) {
    return _contextSorts.get(ta);
  } else {
    unsigned s = env.sorts->addSort("ctx_" + name() + "_" + ta->name(), false);
    _contextSorts.insert(ta, s);
    return s;
  }
}

vstring TermAlgebra::getCstFunctionName(TermAlgebra* ta) {
  return "$cst_" + name() + ta->name();
}

unsigned TermAlgebra::getCstFunction(TermAlgebra* ta) {
  CALL("TermAlgebra::getCstFunction");

  bool added;
  unsigned s = env.signature->addFunction(getCstFunctionName(ta), 1, added);

  if (added) {
    env.signature->getFunction(s)->setType(OperatorType::getFunctionType({_sort}, contextSort(ta)));
  }

  return s;
}

vstring TermAlgebra::getHoleConstantName() {
  return "$hole_" + name();
}

unsigned TermAlgebra::getHoleConstant() {
  CALL("TermAlgebra::getHoleConstant");
  
  bool added;
  unsigned s = env.signature->addFunction(getHoleConstantName(), 0, added);

  if (added) {
    env.signature->getFunction(s)->setType(OperatorType::getConstantsType(contextSort(this)));
  }

  return s;
}

vstring TermAlgebra::getCycleFunctionName() {
  return "$cycle_" + name();
}

unsigned TermAlgebra::getCycleFunction() {
  CALL("TermAlgebra::getCycleFunction");

  bool added;
  unsigned s = env.signature->addFunction(getCycleFunctionName(), 1, added);

  if (added) {
    env.signature->getFunction(s)->setType(OperatorType::getFunctionType({contextSort(this)}, _sort));
  }

  return s;
}

vstring TermAlgebra::getAppFunctionName(TermAlgebra* ta) {
  return "$app_" + name() + "_" + ta->name();
}

unsigned TermAlgebra::getAppFunction(TermAlgebra* ta) {
  CALL("TermAlgebra::getAppFunction");

  bool added;
  unsigned s = env.signature->addFunction(getAppFunctionName(ta), 2, added);

  if (added) {
    env.signature->getFunction(s)->setType(OperatorType::getFunctionType({contextSort(ta), ta->sort()}, _sort));
  }

  return s;
}

void TermAlgebra::setMutualTypes()
{
  CALL("TermAlgebra::setMutualTypes");

  ASS(!_mutualTypes);
  _mutualTypes = new Set<unsigned>();

  // This is a BFS is the tree formed by the algebra declaration (the
  // types of its constructors) to detect cycles (mutually recursive
  // types)
  
  Stack<TermAlgebra*> path; // path in DFS is kept because we need all the vertices in the cycle
  Stack<std::pair<TermAlgebra*, unsigned>> toVisit; // the integer represents the depth of the node in the DFS
  Set<TermAlgebra*> visited;

  // start DFS
  toVisit.push(make_pair(this, 0));

  while (toVisit.isNonEmpty()) {
    std::pair<TermAlgebra*, unsigned> n = toVisit.pop();
    TermAlgebra *ta = n.first;
    unsigned depth = n.second;
    // unstack path
    while (path.size() > depth) {
      path.pop();
    }

    path.push(ta);
    visited.insert(ta);

    for (unsigned i = 0; i < ta->nConstructors(); i++) {
      TermAlgebraConstructor *c = ta->constructor(i);
      for (unsigned j = 0; j < c->arity(); j++) {
        unsigned s = c->argSort(j);
        if (env.signature->isTermAlgebraSort(s)) {
          TermAlgebra* ta2 = env.signature->getTermAlgebraOfSort(s);
          if (ta2 == this || _mutualTypes->contains(s)) {
            // push path into _mutualTypes
            Stack<TermAlgebra*>::Iterator it(path);
            while (it.hasNext()) {
              _mutualTypes->insert(it.next()->sort());
            }
          }
          if (!visited.contains(ta2)) {
            // push adjacent nodes on toVisit with depth + 1
            toVisit.push(make_pair(ta2, depth + 1));
          }
        }
      }
    }
  }

  // since the 'mutual type' relation is symmetric, set the other
  // types' mutualType field to avoid re-computing later
  Set<unsigned>::Iterator it(*_mutualTypes);
  while (it.hasNext()) {
    TermAlgebra *ta = env.signature->getTermAlgebraOfSort(it.next());
    if (ta != this && !ta->_mutualTypes) {
      ta->_mutualTypes = new Set<unsigned>();
      ta->_mutualTypes->insertFromIterator(Set<unsigned>::Iterator(*_mutualTypes));
    }
  }
}

}
