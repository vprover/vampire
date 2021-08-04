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
#include "Kernel/Matcher.hpp"
#include "Kernel/SortHelper.hpp"

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
}

TermAlgebraConstructor::TermAlgebraConstructor(unsigned functor, unsigned discriminator, Lib::Array<unsigned> destructors)
  : _functor(functor), _hasDiscriminator(true), _discriminator(discriminator), _destructors(destructors)
{
  _type = env.signature->getFunction(_functor)->fnType();
  ASS_REP(env.signature->getFunction(_functor)->termAlgebraCons(), env.signature->functionName(_functor));
  ASS_EQ(_type->arity(), destructors.size());
}

//This is only safe for monomorphic term algebras AYB
unsigned TermAlgebraConstructor::arity()               { return _type->arity();  }
TermList TermAlgebraConstructor::argSort(unsigned ith) { return _type->arg(ith); }
TermList TermAlgebraConstructor::rangeSort()           { return _type->result(); }

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

vvector<TermList> TermAlgebra::generateAvailableTerms(const Term* t, unsigned& var) {
  const auto taSort = SortHelper::getResultSort(t);
  const auto ta = env.signature->getTermAlgebraOfSort(taSort);
  vvector<TermList> res;
  Stack<TermList> argTerms;
  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    TermAlgebraConstructor *c = ta->constructor(i);
    argTerms.reset();

    for (unsigned j = 0; j < c->arity(); j++) {
      argTerms.push(TermList(var++, false));
    }

    res.emplace_back(Term::create(c->functor(), argTerms.size(), argTerms.begin()));
  }
  return res;
}

bool TermAlgebra::excludeTermFromAvailables(vvector<TermList>& availables, TermList e, unsigned& var) {
  ASS(e.isTerm());
  auto last = availables.size();
  bool excluded = false;
  for (unsigned i = 0; i < last;) {
    auto p = availables[i];
    // if p is an instance of e, p is removed
    if (MatchingUtils::matchTerms(e, p)) {
      excluded = true;
      availables[i] = availables.back();
      availables.pop_back();
      last--;
    }
    // if e is an instance of p, the remaining
    // instances of p are added
    else if (MatchingUtils::matchTerms(p, e)) {
      excluded = true;
      availables[i] = availables.back();
      availables.pop_back();
      last--;
      vvector<TermList> newTerms;
      if (p.isVar()) {
        newTerms = generateAvailableTerms(e.term(), var);
        excludeTermFromAvailables(newTerms, e, var);
      } else {
        Term::Iterator pIt(p.term());
        Term::Iterator eIt(e.term());
        while (pIt.hasNext()) {
          auto pArg = pIt.next();
          auto eArg = eIt.next();

          // a variable excludes everything,
          // so we only consider terms here
          if (eArg.isTerm()) {
            vvector<TermList> terms;
            if (pArg.isVar()) {
              terms = generateAvailableTerms(eArg.term(), var);
            } else {
              terms.push_back(pArg);
            }
            excludeTermFromAvailables(terms, eArg, var);
            for (auto& r : terms) {
              TermListReplacement tr(pArg, r);
              newTerms.push_back(TermList(tr.transform(p.term())));
            }
          }
        }
      }
      availables.insert(availables.end(), newTerms.begin(), newTerms.end());
    } else {
      i++;
    }
  }
  availables.shrink_to_fit();
  return excluded;
}

}
