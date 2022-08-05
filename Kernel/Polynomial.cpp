/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#include "Kernel/Polynomial.hpp"
#include "Kernel/PolynomialNormalizer.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Kernel {

PolyNf PolyNf::normalize(TypedTermList t)  
{ return normalizeTerm(t); }

////////////////////////////////////////////////////////////////////////////////////////////////////
// impl Variable
/////////////////////////////////////////////////////////

Variable::Variable() : _num() {}

Variable::Variable(unsigned num) : _num(num) {}

unsigned Variable::id() const 
{ return _num; }


bool operator==(Variable lhs, Variable rhs) 
{ return lhs._num == rhs._num; }

bool operator!=(Variable lhs, Variable rhs) 
{ return !(lhs == rhs); }

bool operator<(Variable const& lhs, Variable const& rhs)
{ return lhs._num < rhs._num; }

std::ostream& operator<<(std::ostream& out, const Variable& self) 
{ return out << "X" << self._num; }

////////////////////////////////////////////////////////////////////////////////////////////////////
// impl FuncId
/////////////////////////////////////////////////////////

FuncId::FuncId(unsigned num, TermList const* typeArgs) : _num(num), _typeArgs(std::move(typeArgs)) {}

FuncId FuncId::symbolOf(Term* term) 
{ return FuncId(term->functor(), term->typeArgs()); }

unsigned FuncId::numTermArguments() const
{ return symbol()->numTermArguments(); }

unsigned FuncId::numTypeArguments() const
{ return symbol()->numTypeArguments(); }

TermList FuncId::typeArg(unsigned i) const
{ return _typeArgs[i]; }

std::ostream& operator<<(std::ostream& out, const FuncId& self) 
{ return out << self.symbol()->name(); }

Signature::Symbol* FuncId::symbol() const 
{ return env.signature->getFunction(_num); }

unsigned FuncId::id() const 
{ return _num; }

Theory::Interpretation FuncId::interpretation() const 
{ return theory->interpretFunction(_num); }

bool FuncId::isInterpreted() const
{ return theory->isInterpretedFunction(_num); }

Option<Theory::Interpretation> FuncId::tryInterpret() const
{ 
  return isInterpreted() ? some<Theory::Interpretation>(interpretation())
                         : none<Theory::Interpretation>();
}
} // namespace Kernel

////////////////////////////////////////////////////////////////////////////////////////////////////
// impl FuncTerm
/////////////////////////////////////////////////////////

namespace Kernel {

FuncTerm::FuncTerm(Term* t) 
  : _self(t)
{  }

// FuncTerm::FuncTerm(FuncId f, Stack<PolyNf>&& args) 
//   : _fun(f)
//   , _args(std::move(args)) 
// { }

FuncTerm::FuncTerm(FuncId f, PolyNf* args) 
  : _self(Term::create(f.id(), 
        concatIters(
          f.iterTypeArgs(),
          range(0, f.numTermArguments())
             .map([=](auto i) { return args[i].denormalize(); })
          ).collect <Stack>()
        ))
{ }

unsigned FuncTerm::numTermArguments() const 
{ return _self->numTermArguments(); }

FuncId FuncTerm::function() const 
{ return FuncId(_self->functor(), _self->typeArgs()); }

PolyNf FuncTerm::arg(unsigned i) const 
{ return PolyNf::fromNormalized(TypedTermList(_self->termArg(i), SortHelper::getTermArgSort(_self, i))); }

std::ostream& operator<<(std::ostream& out, const FuncTerm& self) 
{ 
  // TODO nicer outputting?!
  return out << self._self;
  // out << self._fun;
  // auto& stack = self._args;
  // auto iter = stack.iterFifo();
  //
  // if (iter.hasNext()) {
  //   out << "(" << iter.next();
  //   while (iter.hasNext()) {
  //     out << ", " << iter.next();
  //   }
  //   out << ")";
  // }
  //
  // return out;
}


/////////////////////////////////////////////////////////
// impl AnyPoly 
////////////////////////////


AnyPoly AnyPoly::replaceTerms(PolyNf* newTs) const 
{ return apply([&](auto& t) -> decltype(auto) { return AnyPoly(perfect(t->replaceTerms(newTs))); }); }

TermList AnyPoly::denormalize(TermList* results) const
{ return apply([&](auto& t) -> decltype(auto) { return t->denormalize(results); }); }

PolyNf const& AnyPoly::termAt(unsigned summand, unsigned factor)  const
{ return apply([&](auto& t) -> decltype(auto) { return t->summandAt(summand).factors->termAt(factor); }); }

unsigned AnyPoly::nSummands() const 
{ return apply([&](auto& t) -> decltype(auto) { return t->nSummands(); }); }

unsigned AnyPoly::nFactors(unsigned i) const 
{ return apply([&](auto& t) -> decltype(auto) { return t->nFactors(i); }); }

std::ostream& operator<<(std::ostream& out, const AnyPoly& self) 
{ return self.apply([&](auto& t) -> decltype(auto) { return out << *t; }); }


/////////////////////////////////////////////////////////
// impl PolyNf 
////////////////////////////

// TODO
// PolyNf::PolyNf(Perfect<FuncTerm> t) : Coproduct(t) {}
// PolyNf::PolyNf(Variable          t) : Coproduct(t) {}
// PolyNf::PolyNf(AnyPoly           t) : Coproduct(t) {}


std::ostream& operator<<(std::ostream& out, const PolyNf& self)
{ return self._self.apply([&](auto& t) -> decltype(auto) { return out << t; }); }

IterTraits<PolyNf::SubtermIter> PolyNf::iterSubterms() const 
{ return iterTraits(SubtermIter(*this)); }

PolyNf::SubtermIter::SubtermIter(PolyNf p) 
  : _stack(decltype(_stack){ BottomUpChildIter<PolyNf>(p) }) 
{  }

PolyNf PolyNf::SubtermIter::next() 
{
  CALL("PolyNf::SubtermIter::next")
  ASS(_stack.size() != 0)
  while(_stack.top().hasNext()) {
    ASS(_stack.size() != 0)
    _stack.push(BottomUpChildIter<PolyNf>(_stack.top().next()));
  }
  ASS(_stack.size() != 0)
  return _stack.pop().self();
}

bool PolyNf::SubtermIter::hasNext() const 
{ 
  CALL("PolyNf::SubtermIter::hasNext")
  return !_stack.isEmpty(); 
}


/////////////////////////////////////////////////////////
// impl IterArgsPnf
////////////////////////////


IterArgsPnf::IterArgsPnf(Literal* lit) 
  : _lit(lit)
  , _idx(0) 
{ }

bool IterArgsPnf::hasNext() const  
{ return _idx < _lit->numTermArguments();  }

PolyNf IterArgsPnf::next()
{ 
  auto out = PolyNf::normalize(TypedTermList(_lit->termArg(_idx), SortHelper::getTermArgSort(_lit, _idx)));
  _idx++;
  return out;
}

IterTraits<IterArgsPnf> iterArgsPnf(Literal* lit) 
{ return iterTraits(IterArgsPnf(lit)); }

} // namespace Kernel
