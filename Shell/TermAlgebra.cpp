/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Kernel/Formula.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"

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
#if VDEBUG
  ASS_REP(env.signature->getFunction(_functor)->termAlgebraCons(), env.signature->functionName(_functor));
  ASS_EQ(arity(), numTypeArguments()+destructors.size());
  unsigned i = 0;
  for (auto d : destructors) {
    auto sym = argSort(numTypeArguments()+i++) == AtomicSort::boolSort() ? env.signature->getPredicate(d)
                                                                         : env.signature->getFunction(d);
    ASS_REP(sym->termAlgebraDest(), sym->name())
  }
#endif
}

TermAlgebraConstructor::TermAlgebraConstructor(unsigned functor, unsigned discriminator, Lib::Array<unsigned> destructors)
  : _functor(functor), _hasDiscriminator(true), _discriminator(discriminator), _destructors(destructors)
{
  _type = env.signature->getFunction(_functor)->fnType();
#if VDEBUG
  ASS_REP(env.signature->getFunction(_functor)->termAlgebraCons(), env.signature->functionName(_functor));
  ASS_EQ(arity(), numTypeArguments()+destructors.size());
  for (auto d : destructors) {
    ASS(env.signature->getFunction(d)->termAlgebraDest())
  }
#endif
}

//This is only safe for monomorphic term algebras AYB
unsigned TermAlgebraConstructor::arity() const { return _type->arity();  }
unsigned TermAlgebraConstructor::numTypeArguments() const { return _type->numTypeArguments(); }

unsigned TermAlgebraConstructor::discriminator()
{
  if (hasDiscriminator()) {
    return _discriminator;
  } else {
    auto discr = env.signature->addFreshPredicate(numTypeArguments()+1, discriminatorName().c_str());
    Signature::Symbol* pred = env.signature->getPredicate(discr);
    pred->setType(OperatorType::getPredicateType({_type->result()},numTypeArguments()));
    pred->markTermAlgebraDiscriminator();
     _hasDiscriminator = true;
     _discriminator = discr;
    return discr;
  }
}

Lib::Set<TermList> TermAlgebra::subSorts(TermList sort)
{
  ASS(sort.isTerm() && sort.term()->isSort());

  Set<TermList> out; 
  /* connected component finding without recursion */
  TermStack work; // <- stack for simulating recursion
  work.push(sort);
  out.insert(sort);
  while (work.isNonEmpty()) {
    auto t = work.pop();
    auto ta = env.signature->getTermAlgebraOfSort(t);
    Substitution typeSubst;
    ta->getTypeSub(t.term(), typeSubst);
    for (auto cons : ta->iterCons()) {
      for (auto s : cons->iterArgSorts()) {
        s = SubstHelper::apply(s, typeSubst);
        if (!s.isTerm()) { continue; }
        if (!out.contains(s)) {
          out.insert(s);
          if (env.signature->isTermAlgebraSort(s)) {
            work.push(s);
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
  for (unsigned i=0; i < _type->arity(); i++) {
    if (_type->arg(i) == _type->result()) {
      // this constructor has a recursive argument
      return true;
    }
  }
  return false;
}

std::string TermAlgebraConstructor::discriminatorName()
{
  //Giles: the function name may contain quotes so we should remove them
  //       before appending $is.
  std::string name = env.signature->functionName(_functor);
  std::string ret = "$is";
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
  ASS(_sort.isTerm());
  ASS(anyArgIter(_sort.term()).all([](TermList t) { return t.isVar(); }));
  for (unsigned i = 0; i < constrs.size(); i++) {
    ASS_EQ(constrs[i]->rangeSort(), _sort);
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
  ASS(_sort.isTerm());
  ASS(anyArgIter(_sort.term()).all([](TermList t) { return t.isVar(); }));
  for (unsigned i = 0; i < n; i++) {
    ASS_EQ(constrs[i]->rangeSort(), _sort);
    _constrs[i] = constrs[i];
  }
}

bool TermAlgebra::emptyDomain()
{
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
  for (unsigned i = 0; i < _n; i++) {
    if (_constrs[i]->arity() > 0) {
      return false;
    }
  }

  return true;
}

bool TermAlgebra::infiniteDomain()
{
  for (unsigned i = 0; i < _n; i++) {
    if (_constrs[i]->recursive()) {
      return true;
    }
  }

  return false;
}
  
std::string TermAlgebra::getSubtermPredicateName() {
  return "$subterm" + env.signature->getTypeCon(_sort.term()->functor())->name();
}

unsigned TermAlgebra::getSubtermPredicate() {
  bool added;
  unsigned s = env.signature->addPredicate(getSubtermPredicateName(), nTypeArgs()+2, added);

  if (added) {
    // declare a binary predicate subterm
    TermStack args;
    args.push(_sort);
    args.push(_sort);
    env.signature->getPredicate(s)->setType(OperatorType::getPredicateType(args.size(),args.begin(),nTypeArgs()));
  }

  return s;
}

void TermAlgebra::getTypeSub(Term* sort, Substitution& subst)
{
  auto t = _sort.term();
  ASS_EQ(sort->functor(), t->functor());
  for (unsigned i = 0; i < sort->arity(); i++) {
    ASS(t->nthArgument(i)->isVar());
    subst.bindUnbound(t->nthArgument(i)->var(), *sort->nthArgument(i));
  }
}

const InductionTemplate* TermAlgebra::getInductionTemplateOne()
{
  if (!_indTemplOne) {
    Stack<InductionCase> cases;
    auto taArity = nTypeArgs();
    auto typeArgs = TermStack::fromIterator(varRange(0,taArity));
    unsigned var = taArity;

    iterCons()
      .forEach([&](const auto& cons) {
        Stack<InductionUnit> hyps;
        TermStack args = typeArgs;
        for (unsigned i = taArity; i < cons->arity(); i++) {
          args.push(TermList::var(var++));
          if (cons->argSort(i) == cons->rangeSort()) {
            hyps.emplace(TermStack{ args.top() });
          }
        }
        cases.emplace(
          InductionUnit({ TermList(Term::create(cons->functor(),(unsigned)args.size(), args.begin())) }),
          std::move(hyps)
        );
      });
    _indTemplOne = std::make_unique<const InductionTemplate>(
      TermStack{ TermList(AtomicSort::create(_sort.term()->functor(), typeArgs.size(), typeArgs.begin())) },
      std::move(cases),
      InductionUnit({ TermList::var(var++) }), /*maxVar=*/var,
      InferenceRule::STRUCT_INDUCTION_AXIOM_ONE
    );
  }
  return _indTemplOne.get();
}

const InductionTemplate* TermAlgebra::getInductionTemplateTwo()
{
  if (!_indTemplTwo) {
    Stack<InductionUnit> hypotheses;
    auto taArity = nTypeArgs();
    auto typeArgs = TermStack::fromIterator(varRange(0,taArity));
    auto y = TermList::var(taArity);
    auto z = TermList::var(taArity+1);

    iterCons()
      .forEach([&](const auto& cons) {
        if (!cons->recursive()) {
          return;
        }

        TermStack args = typeArgs;
        TermStack taTerms;
        for (unsigned i = taArity; i < cons->arity(); i++) {
          TermStack dargs = typeArgs;
          dargs.push(y);

          unsigned di = cons->destructorFunctor(i - taArity);
          TermList diy = (cons->argSort(i)==AtomicSort::boolSort())
            ? TermList(Term::createFormula(new AtomicFormula(Literal::create(di,dargs.size(),true,dargs.begin()))))
            : TermList(Term::create(di,dargs.size(),dargs.begin()));

          args.push(diy);
          if (cons->argSort(i) == cons->rangeSort()) {
            taTerms.push(diy);
          }
        }
        ASS(taTerms.isNonEmpty());

        for (const auto& t : taTerms) {
          hypotheses.emplace(TermStack{ t },
            LiteralStack{ Literal::createEquality(true, y, TermList(Term::create(cons->functor(), args.size(), args.begin())), cons->rangeSort()) });
        }
      });

    _indTemplTwo = std::make_unique<const InductionTemplate>(
      TermStack{ TermList(AtomicSort::create(_sort.term()->functor(), typeArgs.size(), typeArgs.begin())) },
      Stack<InductionCase>{ { InductionUnit({ y }), std::move(hypotheses) } },
      InductionUnit({ z }), /*maxVar=*/z.var(),
      InferenceRule::STRUCT_INDUCTION_AXIOM_TWO
    );
  }
  return _indTemplTwo.get();
}

const InductionTemplate* TermAlgebra::getInductionTemplateThree()
{
  if (!_indTemplThree) {
    Stack<InductionUnit> hypotheses;
    auto taArity = nTypeArgs();
    auto x = TermList::var(taArity);
    auto y = TermList::var(taArity+1);
    auto z = TermList::var(taArity+2);

    auto typeArgs = TermStack::fromIterator(varRange(0,taArity));
    auto args = typeArgs;
    args.push(x);
    args.push(y);

    auto cond = Literal::create(getSubtermPredicate(), args.size(), true, args.begin());
    hypotheses.push(InductionUnit({ x }, { cond }));

    _indTemplThree = std::make_unique<const InductionTemplate>(
      TermStack{ TermList(AtomicSort::create(_sort.term()->functor(), typeArgs.size(), typeArgs.begin())) },
      Stack<InductionCase>{ { InductionUnit({ y }), std::move(hypotheses), { x.var() } } },
      InductionUnit({ z }), /*maxVar=*/z.var(),
      InferenceRule::STRUCT_INDUCTION_AXIOM_THREE
    );
  }
  return _indTemplThree.get();
}

void TermAlgebra::excludeTermFromAvailables(TermStack& availables, TermList e, unsigned& var)
{
  ASS(e.isTerm() && !e.term()->isLiteral());
  NonVariableIterator nvi(e.term(), true);
  while (nvi.hasNext()) {
    auto symb = env.signature->getFunction(nvi.next().term()->functor());
    if (!symb->termAlgebraCons() && !symb->termAlgebraDest()) {
      return; // we cannot exclude anything non-ctor/dtor
    }
  }
  TermStack temp;
  while (availables.isNonEmpty()) {
    auto p = availables.pop();
    Substitution subst;
    // if e is an instance of p, the remaining
    // instances of p are added
    if (MatchingUtils::matchTerms(p, e, subst)) {
      auto items = subst.items();
      Substitution s;
      while (items.hasNext()) {
        auto kv = items.next();
        s.reset();
        if (kv.second.isTerm()) {
          const auto ta = env.signature->getTermAlgebraOfSort(SortHelper::getResultSort(kv.second.term()));
          if (!ta) {
            continue; // not term algebra sort
          }
          TermStack argTerms;
          for (unsigned i = 0; i < ta->nConstructors(); i++) {
            TermAlgebraConstructor *c = ta->constructor(i);
            argTerms.reset();

            for (unsigned j = 0; j < c->arity(); j++) {
              argTerms.push(TermList(var++, false));
            }

            s.rebind(kv.first, TermList(Term::create(c->functor(), argTerms.size(), argTerms.begin())));
            availables.push(SubstHelper::apply(p, s));
          }
        }
      }
    }
    // otherwise if p is not an instance of e, p is added back
    else if (!MatchingUtils::matchTerms(e, p, subst)) {
      temp.push(p);
    }
  }
  availables.loadFromIterator(temp.iter());
}

std::ostream& operator<<(std::ostream& out, TermAlgebraConstructor const& self) 
{ return out << "ctor " << env.signature->getFunction(self.functor())->name(); }

std::ostream& operator<<(std::ostream& out, TermAlgebra const& self) 
{ return out << "term_algebra " << self.sort().toString(); }

} // namespace Shell
