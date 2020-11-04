
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

FuncId::FuncId(unsigned num) : _num(num) {}

unsigned FuncId::arity() 
{ return symbol()->arity(); }

bool operator==(FuncId const& lhs, FuncId const& rhs) 
{ return lhs._num == rhs._num; }

bool operator!=(FuncId const& lhs, FuncId const& rhs) 
{ return !(lhs == rhs); }

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

Optional<Theory::Interpretation> FuncId::tryInterpret() const
{ 
  return isInterpreted() ? some<Theory::Interpretation>(interpretation())
                         : none<Theory::Interpretation>();
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// impl FuncTerm
/////////////////////////////////////////////////////////

FuncTerm::FuncTerm(FuncId f, Stack<PolyNf>&& args) 
  : _fun(f)
  , _args(std::move(args)) 
{ }

FuncTerm::FuncTerm(FuncId f, PolyNf* args) 
  : _fun(f)
  , _args(Stack<PolyNf>::fromIterator(getArrayishObjectIterator(args, f.arity()))) 
{ }

bool operator==(FuncTerm const& lhs, FuncTerm const& rhs) 
{ return lhs._fun == rhs._fun && lhs._args == rhs._args; }

bool operator!=(FuncTerm const& lhs, FuncTerm const& rhs) 
{ return !(lhs == rhs); }

unsigned FuncTerm::arity() const 
{ return _args.size(); }

FuncId FuncTerm::function() const 
{ return _fun; }

PolyNf const& FuncTerm::arg(unsigned i) const 
{ return _args[i]; }


/////////////////////////////////////////////////////////
// impl AnyPoly 
////////////////////////////


POLYMORPHIC_FUNCTION(AnyPoly, replaceTerms, const& t, PolyNf* newTs;) 
{ return AnyPoly(unique(t->replaceTerms(newTs))); }

AnyPoly AnyPoly::replaceTerms(PolyNf* newTs) const 
{ return apply(Polymorphic::replaceTerms{newTs}); }

TermList AnyPoly::toTerm(TermList* results) const
{ return apply(Polymorphic::toTerm{results}); }

PolyNf const& AnyPoly::termAt(unsigned summand, unsigned factor)  const
{  return apply(Polymorphic::termAt{summand, factor}); }

unsigned AnyPoly::nSummands() const 
{ return apply(Polymorphic::nSummands{}); }

unsigned AnyPoly::nFactors(unsigned i) const 
{ return apply(Polymorphic::nFactors{i}); }

std::ostream& operator<<(std::ostream& out, const AnyPoly& self) 
{ return self.apply(Polymorphic::outputOp{out}); }


/////////////////////////////////////////////////////////
// impl PolyNf 
////////////////////////////


PolyNf::PolyNf(UniqueShared<FuncTerm> t) : Coproduct(t) {}
PolyNf::PolyNf(Variable               t) : Coproduct(t) {}
PolyNf::PolyNf(AnyPoly                t) : Coproduct(t) {}


bool operator==(PolyNf const& lhs, PolyNf const& rhs) 
{ return static_cast<PolyNfSuper const&>(lhs) == static_cast<PolyNfSuper const&>(rhs); }

bool operator!=(PolyNf const& lhs, PolyNf const& rhs) 
{ return !(lhs == rhs); }

std::ostream& operator<<(std::ostream& out, const PolyNf& self)
{ return self.apply(Polymorphic::outputOp{out}); }

TermList PolyNf::toTerm() const
{ 
  CALL("PolyNf::toTerm")
  DEBUG("converting ", *this)
  struct Eval 
  {
    using Arg    = PolyNf;
    using Result = TermList;

    TermList operator()(PolyNf orig, TermList* results)
    { return orig.match(
        [&](UniqueShared<FuncTerm> t) { return TermList(Term::create(t->function().id(), t->arity(), results)); },
        [&](Variable               v) { return TermList::var(v.id()); },
        [&](AnyPoly                p) { return p.toTerm(results); }
        ); }
  };

  static Memo::Hashed<PolyNf, TermList> memo;
  return evaluateBottomUp(*this, Eval{}, memo);
}

Optional<Variable> PolyNf::tryVar() const 
{ return as<Variable>().template innerInto<Variable>(); }

IterTraits<PolyNf::Iter> PolyNf::iter() const 
{ return iterTraits(Iter(*this)); }

// TODO continue here

} // namespace Kernel
