/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"

using namespace Kernel;
using namespace Lib;

namespace Shell {

TermAlgebraConstructor::TermAlgebraConstructor(unsigned functor, std::initializer_list<unsigned> destructors)
  : TermAlgebraConstructor(functor, Lib::Array<unsigned>(destructors))
{ }

TermAlgebraConstructor::TermAlgebraConstructor(unsigned functor, Lib::Array<unsigned> destructors)
  : _functor(functor), _hasDiscriminator(false), _destructors(destructors)
{
  _type = env.signature->getFunction(_functor)->fnType();
  ASS_REP(env.signature->getFunction(_functor)->termAlgebraCons(), env.signature->functionName(_functor));
  ASS_EQ(_type->arity(), destructors.size());
  unsigned i = 0;
  for (auto d : destructors) {
    auto sym = _type->arg(i++) == AtomicSort::boolSort() ? env.signature->getPredicate(d)
                                                   : env.signature->getFunction(d);
    ASS_REP(sym->termAlgebraDest(), sym->name())
  }
}

TermAlgebraConstructor::TermAlgebraConstructor(unsigned functor, unsigned discriminator, Lib::Array<unsigned> destructors)
  : _functor(functor), _hasDiscriminator(true), _discriminator(discriminator), _destructors(destructors)
{
  _type = env.signature->getFunction(_functor)->fnType();
  ASS_REP(env.signature->getFunction(_functor)->termAlgebraCons(), env.signature->functionName(_functor));
  ASS_EQ(_type->arity(), destructors.size());
  for (auto d : destructors) {
    ASS(env.signature->getFunction(d)->termAlgebraDest())
  }
}

//This is only safe for monomorphic term algebras AYB
unsigned TermAlgebraConstructor::arity() const { return _type->arity();  }

unsigned TermAlgebraConstructor::createDiscriminator() 
{
  if (hasDiscriminator()) {
    return discriminator();
  } else {
    auto sym = env.signature->getFunction(functor());
    auto discr = env.signature->addFreshPredicate(1, ( "$$is_" + sym->name() ).c_str());
    env.signature->getPredicate(discr)->setType(OperatorType::getPredicateType({_type->result()}));
    addDiscriminator(discr);
    return discr;
  }
}

Lib::Set<TermList> TermAlgebra::subSorts()
{

  Set<TermList> out; 
  /* connected component finding without recursion */
  Stack<TermAlgebra*> work; // <- stack for simulating recursion
  work.push(this);
  out.insert(this->sort());
  while (!work.isEmpty()) {
    auto& ta = *work.pop();
    for (auto cons : ta.iterCons()) {
      for (auto s : cons->iterArgSorts()) {
        if (!out.contains(s)) {
          out.insert(s);
          if (env.signature->isTermAlgebraSort(s)) {
            work.push(env.signature->getTermAlgebraOfSort(s));
          }
        }
      }
    }
  }
  return out;
}
TermList TermAlgebraConstructor::argSort(unsigned ith) const { return _type->arg(ith); }
TermList TermAlgebraConstructor::rangeSort()           const { return _type->result(); }

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

  //Giles: the function name may contain quotes so we should remove them
  //       before appending $is.
  vstring name = env.signature->functionName(_functor);
  vstring ret = "$is";
  for(size_t i = 0; i < name.size(); i++){
    char c = name[i];
    if(c != '\''){ ret+=c;}
  } 
  return ret;
}

TermAlgebra::TermAlgebra(TermList sort,
                         std::initializer_list<TermAlgebraConstructor*> constrs,
                         bool allowsCyclicTerms) :
  TermAlgebra(sort, Lib::Array<TermAlgebraConstructor*>(constrs), allowsCyclicTerms)
{ }

TermAlgebra::TermAlgebra(TermList sort,
                         Lib::Array<TermAlgebraConstructor*> constrs,
                         bool allowsCyclicTerms) :
  _sort(sort),
  _n(constrs.size()),
  _allowsCyclicTerms(allowsCyclicTerms),
  _constrs(constrs)
{
  for (unsigned i = 0; i < constrs.size(); i++) {
    ASS(constrs[i]->rangeSort() == _sort);
  }
}

TermAlgebra::TermAlgebra(TermList sort,
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
  return "$subterm" + _sort.toString();
}

unsigned TermAlgebra::getSubtermPredicate() {
  CALL("TermAlgebra::getSubtermPredicate");

  bool added;
  unsigned s = env.signature->addPredicate(getSubtermPredicateName(), 2, added);

  if (added) {
    // declare a binary predicate subterm
    TermStack args;
    args.push(_sort); 
    args.push(_sort);
    env.signature->getPredicate(s)->setType(OperatorType::getPredicateType(args.size(),args.begin()));
  }

  return s;
}

std::ostream& operator<<(std::ostream& out, TermAlgebraConstructor const& self) 
{ return out << "ctor " << env.signature->getFunction(self.functor())->name(); }

std::ostream& operator<<(std::ostream& out, TermAlgebra const& self) 
{ return out << "term_algebra " << self.sort().toString(); }

}
