
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

using namespace Kernel;
using namespace Lib;

namespace Shell {

TermAlgebraConstructor::TermAlgebraConstructor(unsigned functor, Lib::Array<unsigned> destructors)
  : _functor(functor), _hasDiscriminator(false), _destructors(destructors)
{
  _type = env.signature->getFunction(_functor)->fnType();
  ASS_REP(env.signature->getFunction(_functor)->termAlgebraCons(), env.signature->functionName(_functor));
  ASS_EQ(_type->arity(), destructors.size());
}

TermAlgebraConstructor::TermAlgebraConstructor(unsigned functor, unsigned discriminator, Lib::Array<unsigned> destructors)
  : _functor(functor), _hasDiscriminator(true), _discriminator(discriminator), _destructors(destructors)
{
  _type = env.signature->getFunction(_functor)->fnType();
  ASS_REP(env.signature->getFunction(_functor)->termAlgebraCons(), env.signature->functionName(_functor));
  ASS_EQ(_type->arity(), destructors.size());
}

unsigned TermAlgebraConstructor::arity()               { return _type->arity();  }
unsigned TermAlgebraConstructor::argSort(unsigned ith) { return _type->arg(ith); }
unsigned TermAlgebraConstructor::rangeSort()           { return _type->result(); }

bool TermAlgebraConstructor::recursive()
{
  CALL("TermAlgebraConstructor::recursive");

  for (unsigned i=0; i < _type->arity(); i++) {
    if (_type->arg(i) == _type->result()) {
      // this constructor has a recursive argument
      return true;
    }
  }
  return false;
}

Lib::vstring TermAlgebraConstructor::discriminatorName()
{
  CALL("TermAlgebraConstructor::discriminatorName");

  return "$is" + env.signature->functionName(_functor);
}

TermAlgebra::TermAlgebra(unsigned sort,
                         unsigned n,
                         TermAlgebraConstructor** constrs,
                         bool allowsCyclicTerms) :
  _sort(sort),
  _n(n),
  _allowsCyclicTerms(allowsCyclicTerms),
  _constrs(n)
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

bool TermAlgebra::finiteDomain()
{
  CALL("TermAlgebra::finiteDomain");

  for (unsigned i = 0; i < _n; i++) {
    if (_constrs[i]->arity() > 0) {
      return false;
    }
  }

  return true;
}

bool TermAlgebra::infiniteDomain()
{
  CALL("TermAlgebra::infiniteDomain");

  for (unsigned i = 0; i < _n; i++) {
    if (_constrs[i]->recursive()) {
      return true;
    }
  }

  return false;
}
  
Lib::vstring TermAlgebra::getSubtermPredicateName() {
  return "$subterm" + env.sorts->sortName(_sort);
}

unsigned TermAlgebra::getSubtermPredicate() {
  CALL("TermAlgebra::getSubtermPredicate");

  bool added;
  unsigned s = env.signature->addPredicate(getSubtermPredicateName(), 2, added);

  if (added) {
    // declare a binary predicate subterm
    Stack<unsigned> args;
    args.push(_sort); args.push(_sort);
    env.signature->getPredicate(s)->setType(OperatorType::getPredicateType(args.size(),args.begin()));
  }

  return s;
}

NatTermAlgebra::NatTermAlgebra(TermAlgebra* ta, unsigned lessPredicate)
  : _ta(ta), _lessPredicate(lessPredicate)
{
  if (ta->nConstructors() != 2) {
    throw BadNatTermAlgebra("nat must have two constructors");
  }
  if (ta->allowsCyclicTerms()) {
    throw BadNatTermAlgebra("nat must not allow cyclic terms (use datatype instead of codatatype)");
  }

  _zero = ta->constructor(0);
  _succ = ta->constructor(1);
  if (_zero->arity() != 0) {
    std::swap(_zero, _succ);
  }
  if (_zero->arity() != 0 || _succ->arity() != 1) {
    throw BadNatTermAlgebra("nat constructors must have arity 0 and 1");
  }
}


}
