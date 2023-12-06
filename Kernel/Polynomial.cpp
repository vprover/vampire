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
#include "Kernel/NumTraits.hpp"
#include "Kernel/PolynomialNormalizer.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Kernel {

PolyNf PolyNf::normalize(TypedTermList t, bool& evaluated)
{ return simplNormalizeTerm(t, evaluated); }

////////////////////////////////////////////////////////////////////////////////////////////////////
// impl Variable
/////////////////////////////////////////////////////////

Variable::Variable() : _num(), _sort() {}

Variable::Variable(unsigned num, TermList sort) : _num(num), _sort(sort) {}

unsigned Variable::id() const 
{ return _num; }

////////////////////////////////////////////////////////////////////////////////////////////////////
// impl FuncId
/////////////////////////////////////////////////////////

FuncId::FuncId(unsigned num, TermList const* typeArgs) : _num(num), _typeArgs(std::move(typeArgs)) {}

FuncId FuncId::symbolOf(Term* term) 
{ return FuncId(term->functor(), term->typeArgs()); }
// { return FuncId(term->functor(), typeArgIter(term).template collect<Stack>()); }

unsigned FuncId::numTermArguments() const
{ return symbol()->numTermArguments(); }

unsigned FuncId::numTypeArguments() const
{ return symbol()->numTypeArguments(); }

TermList FuncId::typeArg(unsigned i) const
{ return _typeArgs[i]; }

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

///////////////////// output operators

std::ostream& operator<<(std::ostream& out, const Kernel::Variable& self) 
{ return out << "X" << self._num; }

std::ostream& operator<<(std::ostream& out, const Kernel::FuncId& self) 
{ return out << self.symbol()->name(); }

std::ostream& operator<<(std::ostream& out, const Kernel::PolyNf& self)
{ return self._self.apply([&](auto& t) -> decltype(auto) { return out << t; }); }

std::ostream& operator<<(std::ostream& out, const Kernel::FuncTerm& self) 
{ 
  out << self.function();
  auto iter = ImmediateSubterms{}(self);

  if (iter.hasNext()) {
    out << "(" << iter.next();
    while (iter.hasNext()) {
      out << ", " << iter.next();
    }
    out << ")";
  }

  return out;
}


std::ostream& operator<<(std::ostream& out, const AnyPoly& self) 
{ return self._self.apply([&](auto& t) -> decltype(auto) { return out << t; }); }


} // namespace Kernel

////////////////////////////////////////////////////////////////////////////////////////////////////
// impl FuncTerm
/////////////////////////////////////////////////////////

namespace Kernel {

FuncTerm::FuncTerm(Term* t) 
  : _self(t)
{  
  forEachNumTraits([&](auto n) {
      using Numeral = typename decltype(n)::ConstantType;
      ASS_REP(!theory->isInterpretedFunction(t, n.addI), *t)
      ASS_REP(!theory->isInterpretedFunction(t, n.minusI), *t)
      ASS_REP(!theory->isInterpretedFunction(t, n.mulI), *t)
      ASS_REP(n.tryNumeral(t).isNone() || n.tryNumeral(t).unwrap() == Numeral(1), *t)
      // ASS(theory->interpretFunction())
  });
}

FuncTerm::FuncTerm(FuncId f, PolyNf* args) 
  : FuncTerm(Term::create(f.id(), 
        concatIters(
          f.iterTypeArgs(),
          range(0, f.numTermArguments())
             .map([=](auto i) { return args[i].denormalize(); })
          ).collect <Stack>()
        ))
{ 
}


void FuncTerm::integrity() const
{ for (unsigned i = 0; i < numTermArguments(); i++) arg(i).integrity(); }

unsigned FuncTerm::numTermArguments() const 
{ return _self->numTermArguments(); }

FuncId FuncTerm::function() const 
{ return FuncId::symbolOf(_self); }

PolyNf FuncTerm::arg(unsigned i) const 
{ return PolyNf::fromNormalized(TypedTermList(_self->termArg(i), SortHelper::getTermArgSort(_self, i))); }

/////////////////////////////////////////////////////////
// impl AnyPoly 
////////////////////////////


AnyPoly AnyPoly::replaceTerms(PolyNf* newTs) const 
{ return _self.apply([&](auto& t) -> decltype(auto) { return AnyPoly(t.replaceTerms(newTs)); }); }

// TermList AnyPoly::denormalize(TermList* results) const
// { return apply([&](auto& t) -> decltype(auto) { return t->denormalize(results); }); }

// PolyNf const& AnyPoly::termAt(unsigned summand, unsigned factor)  const
// { return _self.apply([&](auto& t) -> decltype(auto) { return t.summandAt(summand).factors.termAt(factor); }); }
//
// unsigned AnyPoly::nSummands() const 
// { return _self.apply([&](auto& t) -> decltype(auto) { return t.nSummands(); }); }
//
// unsigned AnyPoly::nFactors(unsigned i) const 
// { return _self.apply([&](auto& t) -> decltype(auto) { return t.nFactors(i); }); }

/////////////////////////////////////////////////////////
// impl PolyNf 
////////////////////////////

PolyNf::PolyNf(FuncTerm t) : _self(std::move(t)) { }
PolyNf::PolyNf(Variable t) : _self(std::move(t)) { }
PolyNf::PolyNf(AnyPoly  t) : _self(std::move(t)) { }

PolyNf PolyNf::fromNormalized(TypedTermList t)
{
  if (t.isTerm()) {
    auto term = t.term();
    auto f = term->functor();
    auto poly = tryNumTraits([&](auto numTraits) {
        using Numeral = typename decltype(numTraits)::ConstantType;
        Numeral dummyRes;
        return numTraits.addF() == f || numTraits.mulF() == f || numTraits.minusF() == f 
             || (theory->tryInterpretConstant(term, dummyRes) && dummyRes != Numeral(1))
                ? some(PolyNf(AnyPoly(Polynom<decltype(numTraits)>::fromNormalized(t))))
                : none<PolyNf>();
        });
    return poly || [&]() { return PolyNf(FuncTerm::fromNormalized(term)); };
  } else {
    return PolyNf(Variable(t.var(), t.sort()));
  }
}

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
