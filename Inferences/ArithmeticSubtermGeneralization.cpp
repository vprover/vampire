#include "Debug/Assertion.hpp"
#include "Inferences/ArithmeticSubtermGeneralization.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#include "Lib/IntUnionFind.hpp"
#include "Lib/Array.hpp"
#include "Kernel/Ordering.hpp"
#include "Shell/Statistics.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Inferences {

/**
 * Rule' 1)
 *   generalize multiplication
 *   C[k * X] 
 *   ------------ 
 *   C[X]
 *   where 
 *   - k is a non-zero number term
 *   - all occurences of X are in terms of the form `k * X`
 *   - sound due to substitution X -> (1/k) * X
 *   - generalization since obviously
 *
 *
 * Rule' 2)
 *   generalize multiplication
 *   C[X + d] 
 *   ------------ 
 *   C[X]
 *   where 
 *   - all occurences of X are in terms of the form `X + d`
 *   - sound due to substitution X -> X - d
 *   - generalization since obviously
 *
 *
 * Algorithm: 
 * Generalization : Meet Semilattice
 * let map : Var -> Generalization
 *
 * // rule 1
 * for term in clause:
 *   for poly in formula:
 *     for summand in poly:
 *        let generalization = summand \ v
 *        if map contains v 
 *          map[v] = map[v] `meet` varCoeff
 *        else              
 *          map[v] = v
 *
 * let (var, gen) = getAnyEntry(map)
 *
 * newClause = {}
 * for term in clause:
 *   term' = term.generalizeBasedOn(gen)
 *   newClause.replace(term, term')
 *
 *
 */

  // TODO move me to different file
class IterArgNfs
{
  Literal* _lit;
  unsigned _idx;
public:
  DECL_ELEMENT_TYPE(PolyNf);

  IterArgNfs(Literal* lit) : _lit(lit), _idx(0) {}

  bool hasNext() const  
  { return _idx < _lit->arity();  }

  PolyNf next()
  { 
    auto out = PolyNf::normalize(TypedTermList(*_lit->nthArgument(_idx), SortHelper::getArgSort(_lit, _idx)));
    _idx++;
    return out;
  }
};

IterTraits<IterArgNfs> iterArgNfs(Literal* lit) 
{ return iterTraits(IterArgNfs(lit)); }


static const auto iterTerms = [](Clause* cl) {
  return iterTraits(cl->iterLits())
    .flatMap([](Literal* lit) { return iterArgNfs(lit); }) 
    .flatMap([](PolyNf arg) { return arg.iter();  });
};

/**
 * Type to erase the NumTraits type parameter from some other template class
 */
template<template<class> class NumberObject>
class AnyNumber : public Coproduct<NumberObject<IntTraits>, NumberObject<RatTraits>, NumberObject<RealTraits> > 
{

public:
  using Super = Coproduct<NumberObject<IntTraits>, NumberObject<RatTraits>, NumberObject<RealTraits>>;
  template<class NumTraits>
  AnyNumber(NumberObject<NumTraits> self) : Super(self) {}

  template<class NumTraits> Optional<NumberObject<NumTraits> const&> downcast() const& { return Super::template as<NumberObject<NumTraits>>(); }
  template<class NumTraits> Optional<NumberObject<NumTraits>      &> downcast()      & { return Super::template as<NumberObject<NumTraits>>(); }
  template<class NumTraits> Optional<NumberObject<NumTraits>     &&> downcast()     && { return Super::template as<NumberObject<NumTraits>>(); }
  
  friend bool operator<(AnyNumber const& lhs, AnyNumber const& rhs)
  { return std::less<Super>{}(lhs,rhs); }
};


static const auto iterPolynoms = [](Clause* cl) {
  return iterTerms(cl)
    .filterMap([](PolyNf subterm) 
        { return subterm.template as<AnyPoly>().template innerInto<AnyPoly>(); });
};


static const auto iterVars = [](Clause* cl) {
  return iterTerms(cl)
    .filterMap([](PolyNf subterm) 
        { return subterm.template as<Variable>().template innerInto<Variable>(); });
};

template<class EvalFn>
pair<Clause*, bool> generalizeBottomUp(Clause* cl, EvalFn eval) 
{
  CALL("generalizeBottomUp")
  /* apply the selectedGen generalization */
  bool anyChange = false;
  bool oneLess = false;
  bool allLessEq = true;

  auto stack = iterTraits(cl->iterLits())
    .map([&](Literal* lit) -> Literal* {
        CALL("generalizeBottomUp(Clause* cl, EvalFn)@closure 1")
        unsigned j = 0;
        auto args = argIter(lit)
          .map([&](TermList term) -> TermList { 
              CALL("generalizeBottomUp(Clause* cl, EvalFn)@closure 2")
              auto norm = PolyNf::normalize(TypedTermList(term, SortHelper::getArgSort(lit, j++)));
              // BuildGeneralizedTerm<Gen> eval { var, generalization };
              auto res = evaluateBottomUp(norm, eval);
              if (res != norm) {
                anyChange = true;
                DEBUG("generalized: ", norm, " -> ", res);
                return res.toTerm();
              } else {
                return term;
              }
          })
          .template collect<Stack>();
        auto generalizedLit = Literal::create(lit, args.begin());

        if (eval.eval.doOrderingCheck) {

          auto ord = Ordering::tryGetGlobalOrdering();
          ASS(ord)
          auto cmp = ord->compare(generalizedLit, lit);
          switch(cmp) {
            case Ordering::LESS:
              oneLess = true;
              break;
            case Ordering::LESS_EQ:
            case Ordering::EQUAL:
              break;
            case Ordering::GREATER:
            case Ordering::GREATER_EQ:
            case Ordering::INCOMPARABLE:
              allLessEq = false;
              DEBUG("ordering violation: ", cmp)
              DEBUG("original   : ", *lit)
              DEBUG("generalized: ", *generalizedLit)
              break;
          }
        }
        return generalizedLit;
    })
    .template collect<Stack>();

  ASS (anyChange) 
  Inference inf(SimplifyingInference1(Kernel::InferenceRule::ARITHMETIC_SUBTERM_GENERALIZATION, cl));
  bool redundant = allLessEq && oneLess;
  env.statistics->asgCnt++;
  if (!redundant) {
    env.statistics->asgViolations++;
  }
  return make_pair(Clause::fromStack(stack, inf), redundant);
}

template<class NumTraits> class GeneralizeAdd;


pair<Clause*, bool> nop(Clause* cl) 
{ return make_pair(cl, false); }

template<class Generalization>
struct ArithmeticSubtermGeneralization
{
  static pair<Clause*,bool> simplify(Clause* cl, bool doCheckOrdering);
};

struct Top {};
struct Bot {};

ostream& operator<<(ostream& out, Bot self) { return out << "bot"; }
ostream& operator<<(ostream& out, Top self) { return out << "top"; }
bool operator==(Top,Top) { return true; }
bool operator==(Bot,Bot) { return true; }

template<template<class> class VarGeneralization> struct VarMap;

template<class NumTraits> struct FnGetInner;
template<class NumTraits> struct FnGetInnerConst;

template<class NumTraits>
void sortByMonom(Stack<PolyPair<NumTraits>>& s)
{ std::sort(s.begin(), s.end()); }

template<class Eval>
struct EvaluateAnyPoly
{
  Eval eval;
  using Arg    = PolyNf;
  using Result = PolyNf;

  PolyNf operator()(PolyNf term, PolyNf* evaluatedArgs) 
  {
    CALL("EvaluateAnyPoly::operator()")
    auto out = term.match(
        [&](UniqueShared<FuncTerm> t) -> PolyNf
        { return unique(FuncTerm(t->function(), evaluatedArgs)); },

        [&](Variable v) 
        { return v; },

        [&](AnyPoly p) 
        { return PolyNf(eval(p, evaluatedArgs)); }
        );
    return out;
  }
};


template<class Eval>
struct EvalPolynomClsr {
  Eval& eval;
  PolyNf* evaluatedArgs;

  template<class NumTraits>
  AnyPoly operator()(UniqueShared<Polynom<NumTraits>> poly)
  { return AnyPoly(eval(poly, evaluatedArgs)); }
};


template<class Eval>
struct EvaluatePolynom
{
  Eval eval;
  using Arg    = PolyNf;
  using Result = PolyNf;

  AnyPoly operator()(AnyPoly poly, PolyNf* evaluatedArgs)
  { 
    CALL("EvaluatePolynom::operator()(AnyPoly, PolyNf*)")
    return poly.apply(EvalPolynomClsr<Eval>{eval, evaluatedArgs}); 
  }

  PolyNf operator()(PolyNf term, PolyNf* evaluatedArgs) 
  {
    CALL("EvaluatePolynom::operator()")
    return EvaluateAnyPoly<EvaluatePolynom>{*this}(term, evaluatedArgs);
  }
};

template<class Eval>
struct EvaluateMonom
{
  Eval eval;
  using Arg    = PolyNf;
  using Result = PolyNf;

  template<class NumTraits>
  UniqueShared<Polynom<NumTraits>> operator()(UniqueShared<Polynom<NumTraits>> poly, PolyNf* evaluatedArgs)
  { 
    CALL("EvaluateMonom::operator()(AnyPoly, PolyNf*)")

    using Polynom   = Kernel::Polynom<NumTraits>;
    using PolyPair  = Kernel::PolyPair<NumTraits>;

    auto offs = 0;
    return unique(Polynom(
                poly->iter()
                 .map([&](PolyPair pair) -> PolyPair { 
                   CALL("EvaluateMonom::clsr01")

                   auto result = eval(pair, &evaluatedArgs[offs]);
                   offs += pair.monom->nFactors();
                   return result;
               })
            .template collect<Stack>()));
  }

  PolyNf operator()(PolyNf term, PolyNf* evaluatedArgs) 
  {
    CALL("EvaluateMonom::operator()")
    return EvaluatePolynom<EvaluateMonom>{*this}(term, evaluatedArgs);
  }
};

template<class Gen>
struct GeneralizePolynom 
{
  Variable &var;
  Gen &generalization;
  bool doOrderingCheck;

  template<class NumTraits> 
  UniqueShared<Polynom<NumTraits>> operator()(UniqueShared<Polynom<NumTraits>> p, PolyNf* generalizedArgs) 
  { return Gen::generalize(var, generalization, p, generalizedArgs); }
};


template<class Gen>
pair<Clause*, bool> ArithmeticSubtermGeneralization<Gen>::simplify(Clause* cl_, bool doOrderingCheck) 
{
  typename Gen::State map;

  /* populate the map, and computing meets */
  auto& cl = *cl_;
  DEBUG("input clause: ", cl);

  for (auto poly : iterPolynoms(cl_)) {
    Gen::addToMap(map, poly);
  }

  /* select an applicable generalization */

  DEBUG("canidated generalizations: ", map)
  using Opt = Optional<typename decltype(map)::Entry&>;
  Opt selected;
  {
    auto iter = map.iter();
    while (iter.hasNext()) {
      auto& gen = iter.next();
      if (!gen.value().isBot()) {
        selected = Opt(gen);
        break;
      }
    }
  }
  if (selected.isNone()) {
    return nop(cl_);
  } 

  auto& var            = selected.unwrap().key();
  auto& generalization = selected.unwrap().value();
  DEBUG("selected generalization: ", var, " -> ", generalization)

  // auto clsr = [&](AnyPoly p, PolyNf* evaluatedArgs) -> AnyPoly 
  // { return Gen::generalize(var,generalization,p,evaluatedArgs); };

  EvaluatePolynom<GeneralizePolynom<Gen>> eval {var, generalization, doOrderingCheck};
  /* apply the selectedGen generalization */
  return generalizeBottomUp(&cl, eval);
}

template<class NumTraits>
class GeneralizeMul
{
public:
  using PolyPair = Kernel::PolyPair<NumTraits>;

  template<class Self>
  static UniqueShared<Polynom<NumTraits>> generalize(
    Variable var,
    Self const& gen, 
    UniqueShared<Polynom<NumTraits>> poly,
    PolyNf* generalizedArgs);

  template<class GenMap, class Self> static void addToMap(GenMap& map, AnyPoly p_);

  template<class Self, class Num2,
           typename std::enable_if<!std::is_same<Num2, NumTraits>::value, int>::type = 0
  > 
  static UniqueShared<Polynom<Num2>> generalize(
    Variable var,
    Self const& gen, 
    UniqueShared<Polynom<Num2>> poly,
    PolyNf* generalizedArgs) 
  { return unique(poly->replaceTerms(generalizedArgs)); }
};


template<class NumTraits>
class GeneralizeMulNumeral 
{
  using Inner = Coproduct<typename NumTraits::ConstantType, Bot>;
  Inner _inner;
  using PolyPair = Kernel::PolyPair<NumTraits>;
  using Const = typename NumTraits::ConstantType;
  using Monom = Kernel::Monom<NumTraits>;

private:
  GeneralizeMulNumeral(Bot b) : _inner(b) {}
public:
  using Self = GeneralizeMulNumeral;
  GeneralizeMulNumeral& operator=(GeneralizeMulNumeral&&) = default;
  GeneralizeMulNumeral(GeneralizeMulNumeral&&) = default;

  static GeneralizeMulNumeral bot() { return GeneralizeMulNumeral(Bot{}); }
  GeneralizeMulNumeral(Const c);

  GeneralizeMulNumeral meet(GeneralizeMulNumeral&& rhs) && {
    auto& lhs = *this;

    if (lhs._inner.template is<Bot>()) return bot();
    if (rhs._inner.template is<Bot>()) return bot();

    return meet(lhs._inner.template unwrap<Const>(), rhs._inner.template unwrap<Const>());
  }

  bool isBot() const 
  {return _inner.template is<Bot>(); }

  PolyPair cancel(PolyPair p) const;

  friend ostream& operator<<(ostream& out, GeneralizeMulNumeral const& self) 
  { return out << self._inner; }

  template<class Num2> 
  static UniqueShared<Polynom<Num2>> generalize(
    Variable var,
    GeneralizeMulNumeral<Num2> const& gen, 
    UniqueShared<Polynom<Num2>> poly,
    PolyNf* generalizedArgs) 
  { return GeneralizeMul<Num2>::generalize(var, gen, poly, generalizedArgs); }


  static PolyPair generalize(
    Variable var,
    Self const& gen, 
    PolyPair const& poly,
    PolyNf* generalizedArgs);

  template<class GenMap> static void addToMap(GenMap& map, AnyPoly p)
  { return GeneralizeMul<NumTraits>::template addToMap<GenMap, Self>(map, p); }

  template<class GenMap> static void addToMap(GenMap& map, PolyPair const& m);

private:
  static GeneralizeMulNumeral meet(Const lhs, Const rhs) {
    if(lhs == rhs) return GeneralizeMulNumeral(lhs);
    else return bot();
  }
};


template<class A>
class FlatMeetLattice 
{
  using Inner = Coproduct<A, Bot>;
  Inner _inner;
  using PolyPair = Kernel::PolyPair<RealTraits>;
  using Const = RealConstantType;
  using Monom = Kernel::Monom<RealTraits>;

private:
  FlatMeetLattice(Bot b) : _inner(b) {}
public:
  static FlatMeetLattice bot() { return FlatMeetLattice(Bot{}); }

  FlatMeetLattice(A c) : _inner(c) {}

  FlatMeetLattice meet(FlatMeetLattice rhs) 
  {
    auto& lhs = *this;

    if (lhs._inner.template is<Bot>()) return bot();
    if (rhs._inner.template is<Bot>()) return bot();

    return meet(lhs._inner.template unwrap<int>(), rhs._inner.template unwrap<int>());
  }

  bool isBot() const 
  {return _inner.template is<Bot>(); }

  A const& unwrap() const
  { return _inner.template unwrap<A>(); }

  friend ostream& operator<<(ostream& out, FlatMeetLattice const& self) 
  { return out << self._inner; }

private:
  static FlatMeetLattice meet(A lhs, A rhs) {
    if(lhs == rhs) return FlatMeetLattice(lhs);
    else return bot();
  }
};


template<class NumTraits>
GeneralizeMulNumeral<NumTraits>::GeneralizeMulNumeral(Const c) 
    : _inner(
      c == Const(1) || c == Const(0) ? Inner(Bot{}) 
                                     : Inner(c))
  {  }

template<>
GeneralizeMulNumeral<IntTraits>::GeneralizeMulNumeral(Const c) 
    : _inner(
      c == Const(-1) ? Inner(c) 
                     : Inner(Bot{}))
  {  }

template<class NumTraits>
template<class Self>
UniqueShared<Polynom<NumTraits>> GeneralizeMul<NumTraits>::generalize(
  Variable var,
  Self const& gen, 
  UniqueShared<Polynom<NumTraits>> poly,
  PolyNf* generalizedArgs) 
{

  using Polynom   = Kernel::Polynom<NumTraits>;
  using PolyPair  = Kernel::PolyPair<NumTraits>;

  auto offs = 0;
  return unique(Polynom(
              poly->iter()
               .map([&](PolyPair pair) -> PolyPair { 
                 auto result = Self::generalize(var, gen, pair, &generalizedArgs[offs]);
                 offs += pair.monom->nFactors();
                 return result;
             })
          .template collect<Stack>()));
}


template<class NumTraits>
PolyPair<NumTraits> GeneralizeMulNumeral<NumTraits>::generalize(
  Variable var,
  Self const& gen, 
  PolyPair const& pair,
  PolyNf* generalizedArgs) 
{

  using PolyPair  = Kernel::PolyPair<NumTraits>;
  using MonomPair = MonomPair<NumTraits>;

  auto found = (pair.monom->iter()
      .find([&](MonomPair& monom) 
        { return monom == MonomPair(var, 1); }));

  auto newMonom = unique(pair.monom->replaceTerms(generalizedArgs));

  auto p = PolyPair(pair.coeff, newMonom);

  if (found.isSome()) {
     return gen.cancel(p);
  } else {
     return p;
  }
}


template<class NumTraits>
PolyPair<NumTraits> GeneralizeMulNumeral<NumTraits>::cancel(PolyPair p) const 
{ 
   if (_inner.template is<Const>() && _inner != decltype(_inner)(Const(0))) {
      return PolyPair(Const(1), p.monom);
   } else {
      ASS(_inner.template is<Bot>());
      return PolyPair(p.coeff, p.monom);
   }
}

template<class C>
Stack<C> intersectSortedStack(Stack<C>&& l, Stack<C>&& r) 
{
  CALL("intersectSortedStack")
  // DEBUG("lhs: ", l)
  // DEBUG("rhs: ", r)

  if (l.size() == 0) return std::move(l);
  if (r.size() == 0) return std::move(r);

  auto outOffs = 0;
  auto& out = l.size() <= r.size() ? l : r;
  auto loffs = 0;
  auto roffs = 0;
  while (loffs < l.size() && roffs < r.size()) {
    if (l[loffs] == r[roffs]) {
      out[outOffs++] = l[loffs];
      loffs++;
      roffs++;
    } else if(l[loffs] < r[roffs]) {
      loffs++;
    } else {
      roffs++;
    }
  }
  
  out.truncate(outOffs);
  //DEBUG("out: ", out);
  return std::move(out);
}

// template<class NumTraits>
// GeneralizeMulMultiVar<NumTraits> GeneralizeMulMultiVar<NumTraits>::meet(GeneralizeMulMultiVar&& rhs) &&
// {
//   auto& lhs = *this;
//   return GeneralizeMulMultiVar(intersectSortedStack(std::move(lhs._vars), std::move(rhs._vars)));
// }

template<class NumTraits>
class GeneralizeAdd 
{
  using PolyPair = Kernel::PolyPair<NumTraits>;
  using Const = typename NumTraits::ConstantType;
  using Monom = Kernel::Monom<NumTraits>;

  // TODO get rid of this field
  Stack<PolyPair> _cancellable;

  GeneralizeAdd(decltype(_cancellable) cancel) : _cancellable(cancel) {}

public:
  using Lattice = GeneralizeAdd;
  GeneralizeAdd& operator=(GeneralizeAdd&&) = default;
  GeneralizeAdd(GeneralizeAdd&&) = default;
  ~GeneralizeAdd() { CALL("~GeneralizeAdd()") }

  static GeneralizeAdd bot() 
  { return GeneralizeAdd(decltype(_cancellable){}); }

  GeneralizeAdd(Variable var, UniqueShared<Polynom<NumTraits>> poly) : GeneralizeAdd(decltype(_cancellable)()) 
  {
    _cancellable.reserve(poly->nSummands() - 1);
    for (auto const& pair : poly->iter()) {
      if (pair.tryVar() != some(var)) {
        _cancellable.push(pair);
      }
    }
    sortByMonom(_cancellable);
  }

  GeneralizeAdd meet(GeneralizeAdd&& rhs) && {
    CALL("GeneralizeAdd::meet")
    auto& lhs = *this;
    return GeneralizeAdd(intersectSortedStack(std::move(lhs._cancellable), std::move(rhs._cancellable)));
  }

  bool isBot() const { return _cancellable.isEmpty(); }

  friend ostream& operator<<(ostream& out, GeneralizeAdd const& self)
  { return out << self._cancellable; }

  GeneralizeAdd diff(GeneralizeAdd const& rm_) && {
    CALL("GeneralizeAdd::diff")
    // DEBUG("in: ", *this, " - ", rm_)
    auto rm = rm_._cancellable;
 
    auto resOffs  = 0;
    auto rmOffs   = 0;
    auto thisOffs = 0;
    while (rmOffs < rm.size() && thisOffs < _cancellable.size() ) {
      if (rm[rmOffs] == _cancellable[thisOffs]) {
        thisOffs++;
      } else if (rm[rmOffs] < _cancellable[thisOffs]) {
        rmOffs++;
      } else {
        _cancellable[resOffs++] = _cancellable[thisOffs++];
      }
    }
    while (thisOffs < _cancellable.size()) {
      _cancellable[resOffs++] = _cancellable[thisOffs++];
    }
    _cancellable.truncate(resOffs);

    // DEBUG("out: ", *this)
    return std::move(*this);
  }

  static UniqueShared<Polynom<NumTraits>> generalize(
    Variable var,
    GeneralizeAdd<NumTraits> const& gen, 
    UniqueShared<Polynom<NumTraits>> poly,
    PolyNf* generalizedArgs);

  template<class Num2,
           typename std::enable_if<!std::is_same<Num2, NumTraits>::value, int>::type = 0
  > 
  static UniqueShared<Polynom<Num2>> generalize(
    Variable var,
    GeneralizeAdd<Num2> const& gen, 
    UniqueShared<Polynom<Num2>> poly,
    PolyNf* generalizedArgs) 
  { return unique(poly->replaceArgs(generalize)); }

  template<class GenMap>
  static void addToMap(GenMap& map, AnyPoly p_);

};



template<class NumTraits>
UniqueShared<Polynom<NumTraits>> GeneralizeAdd<NumTraits>::generalize(
  Variable var,
  GeneralizeAdd<NumTraits> const& gen, 
  UniqueShared<Polynom<NumTraits>> poly,
  PolyNf* generalizedArgs) 
{

  CALL("GeneralizeAdd::generalize")
  using PolyPair = Kernel::PolyPair<NumTraits>;

  //TODO memo

  auto found = poly->iter()
    .find([&](PolyPair p) 
        { return p.tryVar() == some(var); });
  if (found.isNone()) {
    return unique(poly->replaceTerms(generalizedArgs));
  }
  auto& toCancel = gen._cancellable;


  Stack<PolyPair> out(poly->nSummands() - toCancel.size());

  unsigned p = 0;
  unsigned genOffs = 0;

  auto pushGeneralized = [&]()  
  { 
    auto monom = unique(poly->summandAt(p).monom->replaceTerms(&generalizedArgs[genOffs]));
    auto coeff = poly->summandAt(p).coeff;

    genOffs += monom->nFactors();
    p++;

    return out.push(PolyPair(coeff, monom));
  };

  auto skipGeneralized = [&]() 
  {
    genOffs += poly->summandAt(p).monom->nFactors();
    p++;
  };

  unsigned c = 0; 
  while (c < toCancel.size() && poly->summandAt(p) < toCancel[c]  ) {
    pushGeneralized();
  }
  while (p < poly->nSummands() && c < toCancel.size()) {
    if (toCancel[c] == poly->summandAt(p)) {
      skipGeneralized();
      c++;
    } else {
      ASS_L(poly->summandAt(p), toCancel[c]);
      pushGeneralized();
    }
  }
  while (p < poly->nSummands()) {
    pushGeneralized();
  }

  return unique(Polynom<NumTraits>(std::move(out)));
}



template<class NumTraits>
template<class GenMap>
void GeneralizeAdd<NumTraits>::addToMap(GenMap& map, AnyPoly p_)
{
  CALL("GeneralizeAdd::addToMap")
  if (!p_.template isType<NumTraits>()) {
    return;
  }
  auto p = p_.template unwrapType<NumTraits>();

  for (auto summand : p->iter()) {
    auto var = summand.tryVar();
    if (var.isSome()) {
      auto v = var.unwrap();
      auto gen = GeneralizeAdd<NumTraits>(v, p);
      map.updateOrInit(v,
          [&](GeneralizeAdd<NumTraits> old) { return move(old).meet(move(gen)); },
          [&]()                             { return move(gen); });
    } else {
      for (auto factor : summand.monom->iter()) {
         if (factor.term.template is<Variable>()) {
           auto v = factor.term.template unwrap<Variable>();
           map.replaceOrInsert(v, GeneralizeAdd<NumTraits>::bot());
         }
      }
    }
  }
}

template<class NumTraits>
template<class GenMap>
void GeneralizeMulNumeral<NumTraits>::addToMap(GenMap& map, PolyPair const& summand)
{
  for (auto factor : summand.monom->iter()) {
    factor.term.template as<Variable>()
      .andThen([&](Variable var) {
          if (factor.power == 1) {
            auto gen = Self(summand.coeff);
            auto entry = map.tryGet(var);
            if (entry.isSome()) {
              auto& val = entry.unwrap();
              val = move(val).meet(std::move(gen));
            } else {
              map.replaceOrInsert(var, std::move(gen));
            }
          } else {
            ASS_G(factor.power, 0)
            map.replaceOrInsert(var, Self::bot());
          }
        });
  }
}

template<class NumTraits>
template<class GenMap, class Self>
void GeneralizeMul<NumTraits>::addToMap(GenMap& map, AnyPoly p_)
{
  if (!p_.template isType<NumTraits>()) {
    return;
  }
  auto p = p_.template unwrapType<NumTraits>();

  for (auto summand : p->iter()) {
    Self::addToMap(map, summand);
  }
};

POLYMORPHIC_FUNCTION(bool,    isBot, const& t,) { return t.isBot(); }

template<template<class> class Gen> 
class ParallelNumberGeneralization;

template<template<class> class Gen> 
struct MapWrapper 
{
  using Value = ParallelNumberGeneralization<Gen>;
  Map<Variable, ParallelNumberGeneralization<Gen>>& self;

  template<class C>
  void replaceOrInsert(Variable var, C&& c) 
  { self.replaceOrInsert(var, Value(std::move(c))); }

  template<class Update, class Init>
  void updateOrInit(Variable var, Update update, Init init)
  { 
    using C = typename std::result_of<Init()>::type;
    self.updateOrInit(var, 
        [&](Value&& c) { return update(std::move(c._inner). template unwrap<C>()); }, 
        init); 
  }

  Optional<ParallelNumberGeneralization<Gen>&> tryGet(Variable var) 
  { return self.tryGet(var); }

  friend ostream& operator<<(ostream& out, MapWrapper const& self)
  { return out << self.self; }
};

template<template<class> class Gen> 
class ParallelNumberGeneralization 
{
public:
  using Inner = Coproduct<Gen<IntTraits>, Gen<RatTraits>, Gen<RealTraits>>;
  template<template<class> class Gen_> 
  friend struct MapWrapper;
private:

  Inner _inner;
public:
  using Self = ParallelNumberGeneralization;

  using State = Map<Variable, Self>;

  template<class C> ParallelNumberGeneralization(Gen<C>&& inner) : _inner(std::move(inner)) {}


  static void addToMap(Map<Variable, Self>& map_, AnyPoly p) 
  {
    MapWrapper<Gen> map { map_ };
    return p.match(
        [&](UniqueShared<Polynom< IntTraits>>const& p)
        { return Gen<IntTraits>::addToMap(map, p); },

        [&](UniqueShared<Polynom< RatTraits>>const& p)
        { return Gen<RatTraits>::addToMap(map, p); },

        [&](UniqueShared<Polynom<RealTraits>>const& p)
        { return Gen<RealTraits>::addToMap(map, p); }
      );
  }

  bool isBot() const { return _inner.apply(Polymorphic::isBot{}); }

  friend ostream& operator<<(ostream& out, ParallelNumberGeneralization const& self)
  { return out << self._inner; }

  template<class NumTraits>
  static UniqueShared<Polynom<NumTraits>> generalize(
    Variable var,
    ParallelNumberGeneralization const& gen, 
    UniqueShared<Polynom<NumTraits>> poly,
    PolyNf* generalizedArgs) 
  {  
    if (gen._inner.template is<Gen<NumTraits>>()) {
      return Gen<NumTraits>::generalize(var, gen._inner.template unwrap<Gen<NumTraits>>(), poly, generalizedArgs); 
    } else {
      return unique(poly->replaceTerms(generalizedArgs));
    }
  }

  ParallelNumberGeneralization meet(ParallelNumberGeneralization&& rhs) && 
  {
    return move(_inner).match(
        [&](Gen< IntTraits>&& lhs) -> ParallelNumberGeneralization
        { return move(lhs).meet(move(rhs._inner).template unwrap<Gen<IntTraits>>()); },

        [&](Gen< RatTraits>&& lhs) -> ParallelNumberGeneralization
        { return move(lhs).meet(move(rhs._inner).template unwrap<Gen<RatTraits>>()); },

        [&](Gen<RealTraits>&& lhs) -> ParallelNumberGeneralization
        { return move(lhs).meet(move(rhs._inner).template unwrap<Gen<RealTraits>>()); }
        );
  }
};

pair<Clause*,bool> AdditionGeneralization::simplify(Clause* cl, bool doOrderingCheck) 
{ 
  CALL("AdditionGeneralization::simplify")
  return ArithmeticSubtermGeneralization<ParallelNumberGeneralization<GeneralizeAdd>>::simplify(cl, doOrderingCheck); 
}

AdditionGeneralization::~AdditionGeneralization()  {}

template<class NumTraits>
using GenMulNum = GeneralizeMulNumeral<NumTraits>;

namespace Rule2 
{

} // namespace Rule2

pair<Clause*, bool> NumeralMultiplicationGeneralization::simplify(Clause* cl, bool doOrderingCheck) 
{ 
  CALL("NumeralMultiplicationGeneralization::simplify")
  return ArithmeticSubtermGeneralization<ParallelNumberGeneralization<GenMulNum>>::simplify(cl, doOrderingCheck); 
}

NumeralMultiplicationGeneralization::~NumeralMultiplicationGeneralization()  {}



/**
 *  Rule 3)
 *    generalize variable multiplication
 *    C[X0 ⋅ X1 ⋅ ... ⋅ Xn] 
 *    ------------ 
 *    C[X0]
 *    where 
 *    - all occurences of Xi are in terms of the form `X0 ⋅ X1 ⋅ ... ⋅ Xn`
 *    - X0 /= Xi (for i /= 0)
 *    - all Xi are distinct variables
 *    - sound due to substitution { X1 -> 1 ..., XN -> 1 }
 *    - obviously a generalization 
 */
namespace Rule3 
{
  POLYMORPHIC_FUNCTION(Optional<Variable>, tryVar, const& t,) { return t.tryVar(); }

  /** 
   * Type for associating objects with integer ids. It is mainly only used in order to use IntUnionFind with other types than int.
   */
  template<class A>
  class IntMap
  {
    Map<A, unsigned> _map;
    Stack<A> _stack;
  public:
    unsigned insert(A obj) 
    {
      return _map.getOrInit(std::move(obj), [&](){ 
        auto idx = _stack.size();
        _stack.push(obj);
        return idx; 
      });
    }

    unsigned size() const 
    { return _stack.size(); }

    unsigned toInt(A const& obj) const
    { return _map.get(obj); }

    A const& fromInt(int obj)  const
    { return _stack[obj]; }
  };



  /**
   * Represents the region of variables `X0 ⋅ X1 ⋅ ... ⋅ Xn` from the rule
   *
   * Two regions can be intersected. 
   */
  class VariableRegion 
  {
    Coproduct<
      Stack<AnyNumber<MonomPair>>, /* <- always sorted; contains only factors of the form `variable ^ n` */
      Top /* <- unininitialized */
        > _self;

  public:
    VariableRegion() : _self(Top{}) {}
    VariableRegion(Stack<AnyNumber<MonomPair>>&& self) : _self(self) {}
    VariableRegion(VariableRegion &&) = default;
    VariableRegion& operator=(VariableRegion &&) = default;

    /* intersects two regions */
    VariableRegion meet(VariableRegion rhs) 
    {
      auto& lhs = *this;
      if (lhs.isUninit()) return VariableRegion(move(rhs));
      if (rhs.isUninit()) return VariableRegion(move(lhs));
      return VariableRegion(intersectSortedStack(std::move(lhs.unwrap()), std::move(rhs.unwrap())));
    }

    Stack<AnyNumber<MonomPair>> const& unwrap() const 
    { return _self.template unwrap<Stack<AnyNumber<MonomPair>>>(); }

    Stack<AnyNumber<MonomPair>> & unwrap() 
    { return _self.template unwrap<Stack<AnyNumber<MonomPair>>>(); }

    friend ostream& operator<<(ostream& out, VariableRegion const& self) 
    {
      return self.isUninit() ? out << "Top"
                          : out << self.unwrap();
    }

    bool isUninit() const 
    { return _self.template is<Top>(); }

    bool isInit() const 
    { return !isUninit(); }
  };


  /**
   * Polymorphic closure that processes each subterm of the clause. 
   *
   * All variables that occur together in a product (i.e. a monom), are being associated with the same "connected component" 
   * using the IntUnionFind components.
   *
   * For each of these components a minimal VariableRegion is kept stored in the field varRegions.
   */
  struct Preprocess 
  {
    IntUnionFind& components;
    IntMap<Variable> &varMap;
    Stack<VariableRegion> &varRegions;

    VariableRegion& varSet(int v)
    { return varRegions[v]; }

    int root(Variable v) const
    { return components.root(varMap.toInt(v)); }

    template<class NumTraits> 
    void operator()(UniqueShared<Polynom<NumTraits>> p) 
    {
      CALL("Preprocess::operator()")

      for (auto summand : p->iter()) {

        auto varIter = summand.monom->iter()
              .filter([](MonomPair<NumTraits> factor) { return factor.term.template is<Variable>(); });

        auto varIter2 = varIter;
        auto varStack = VariableRegion(
            varIter2
              .map([](MonomPair<NumTraits> factor) { return AnyNumber<MonomPair>(factor); })
              .template collect<Stack>());

        auto vars = varIter.map([](MonomPair<NumTraits> factor) { return factor.term.template unwrap<Variable>(); });

        if (vars.hasNext())  {
          auto fst = vars.next();
          auto cur = root(fst);


          varSet(cur) = std::move(varSet(cur)).meet(move(varStack));

          for (auto var : vars) {
            cur = unionMeet(cur, root(var));
          }

        }
      }
    }

    void dbgState() const {
      DEBUG("---------------------");
      for (int i = 0; i < varMap.size(); i++) {
        DEBUG(varMap.fromInt(i), " -> ", varMap.fromInt(components.root(i)), " -> ", varRegions[components.root(i)]);
      }
      DEBUG("---------------------");
    }

    int unionMeet(int v, int w)
    {
      CALL("Preprocess::unionMeet()")
      if (v == w) return v;

      components.doUnion(v,w);
      auto r = components.root(v);
      varSet(r) = std::move(varSet(v)).meet(std::move(varSet(w)));

      return r;
    }

  };

  /** 
   * A polymorphic closure to bottom-up evaluate clause bottom-up that replaces all occurences of the factors in the field `toRem`
   */
  struct Generalize 
  {
    Stack<AnyNumber<MonomPair>> const& toRem; /* <- always expected to be sorted */
    bool doOrderingCheck;

    template<class NumTraits>
    PolyPair<NumTraits> operator()(PolyPair<NumTraits> p, PolyNf* evaluatedArgs)  
    {
      CALL("Generalize::operator()")
      using Pair = PolyPair<NumTraits>;
      return Pair(p.coeff, unique(Monom<NumTraits>(filter(p.monom, evaluatedArgs))));
    }

    template<class NumTraits>
    Stack<MonomPair<NumTraits>> filter(UniqueShared<Monom<NumTraits>> const& monom, PolyNf* evaluatedArgs)
    {
      Stack<MonomPair<NumTraits>> out;
      unsigned rmI = 0;
      unsigned m = 0;

      auto skip = [&]() { rmI++; m++; };
      auto push = [&]() { out.push(MonomPair<NumTraits>(evaluatedArgs[m], monom->factorAt(m).power)); m++; };


      while (m < monom->nFactors() && rmI < toRem.size()) {
        auto factor = monom->factorAt(m);
        auto rm = toRem[rmI].template downcast<NumTraits>();
        if (rm.isNone()) {
          push();
        } else if (factor == rm.unwrap()) {
          skip();
        } else if (factor < rm.unwrap()) {
          push();
        } else {
          ASS_L(rm.unwrap(), factor)
          rmI++;
        }
      }
      while (m < monom->nFactors()) {
        push();
      }

      std::sort(out.begin(), out.end());
      return move(out);
    }
  };

  /** 
   * applies the rule
   */ 
  pair<Clause*,bool> applyRule(Clause* cl, bool doOrderingCheck) 
  {
    DEBUG("input clause: ", *cl);
    IntMap<Variable> varMap;

    /* initialization */
    for (auto var : iterVars(cl)) {
      varMap.insert(var);
    }
    if (varMap.size() == 0) {
      DEBUG("no variables. generalization not applicable");
      return nop(cl);
    }

    IntUnionFind components(varMap.size());
    Stack<VariableRegion> varRegions(varMap.size());;
    for (unsigned i = 0; i < varMap.size(); i++)  {
      varRegions.push(VariableRegion());
    }

    /* preprocessing. finds all products `X0 ⋅ X1 ⋅ ... ⋅ Xn` such that the rule is applicable */
    for (auto poly : iterPolynoms(cl)) {
      poly.apply(Preprocess {components, varMap, varRegions});
    }


    /* create a stack of all variables that shall be removed in the final step */

    Stack<AnyNumber<MonomPair>> remove;

    components.evalComponents();
    for (auto comp : iterTraits(IntUnionFind::ComponentIterator(components))) {
      auto& maybeRegion = varRegions[components.root(comp.next())];
      if (maybeRegion.isInit()) {
        auto& region = maybeRegion.unwrap();

        /* one variable with power one needs to be kept, per varible region */
        auto var = iterTraits(region.iter())
          .filter([](AnyNumber<MonomPair> p) { return p.apply(Polymorphic::tryVar{}).isSome(); })
          .tryNext();

        if (var.isSome()) {
          for (auto varPower : region) {
            if (varPower != var.unwrap()) {
              remove.push(varPower);
            }
          }
        }
      }
    }

    /* apply the substitution `X0 ⋅ X1 ⋅ ... ⋅ Xn ==> X0`  */
    DEBUG("removing variables: ", remove)
    if (remove.isEmpty()) {
      return nop(cl);
    } else {
      std::sort(remove.begin(), remove.end());
      Generalize gen { remove, doOrderingCheck };
      return generalizeBottomUp(cl, EvaluateMonom<Generalize> {gen});
    }
  }

} // namespace Rule3 


/**
 *  Rule 4)
 *    generalize variable multiplication (REALS only)
 *    C[X ⋅ X ⋅ ... ⋅ X ] 
 *    ------------ 
 *    C[X]
 *    where 
 *    - all occurences of X are in terms of the form `X ⋅ X ⋅ ... ⋅ X` 
 *    - sound due to substitution { X -> X^(0/n) }
 *    - obviously a generalization 
 */
namespace Rule4 
{

  using IntLattice = FlatMeetLattice<int>;
  using PowerMap = Map<Variable, IntLattice>;
  template<class Num>
  using EnableIfNotReal = typename std::enable_if<!std::is_same<Num, RealTraits>::value, int>::type;

  /** 
   * Polymorphic closure for preprocessing for the rule application.
   *
   * Collects for each variable the power in which it occurs or Bot when the variable occurs in different powers
   */
  struct Preprocess 
  {
    PowerMap &powers;

    void operator()(UniqueShared<Polynom<RealTraits>> p) 
    {
      for (auto summand : p->iter()) {
        for (auto factor : summand.monom->iter()) {
          auto var = factor.term.tryVar();
          if (var.isSome()) {


            auto current = factor.power == 0 || factor.power == 1  /* <- power 0 should never happen. 
                                                                         power 1 yields a nop-generalization */
              ? IntLattice::bot()
              : IntLattice(factor.power);

            powers.updateOrInit(var.unwrap(),
                [&](IntLattice old) { return current.meet(old); },
                [&]() { return current; }
              );
          }
        }
      }
    }


    template<class Num, EnableIfNotReal<Num> = 0> 
    void operator()(UniqueShared<Polynom<Num>> p) 
    { }

  };

  struct Generalize 
  {
    PowerMap& powers;
    bool doOrderingCheck;

    PolyPair<RealTraits> operator()(PolyPair<RealTraits> p, PolyNf* evaluatedArgs)  
    {
      unsigned i = 0;
      return PolyPair<RealTraits>(
          p.coeff, 
          unique(Monom<RealTraits>(
            p.monom->iter()
             .map([&](MonomPair<RealTraits> m) 
               { 
                  auto var = m.term.tryVar();
                  if (var.isSome() && !powers.get(var.unwrap()).isBot()) {
                    ASS_EQ(evaluatedArgs[i], var.unwrap());
                    return MonomPair<RealTraits>(evaluatedArgs[i++], 2 - ( m.power % 2 ));
                  } else {
                    return MonomPair<RealTraits>(evaluatedArgs[i++], m.power); 
                  }
                })
             .template collect<Stack>())));
    }

    template<class Num, EnableIfNotReal<Num> = 0>
    PolyPair<Num> operator()(PolyPair<Num> p, PolyNf* evaluatedArgs)  
    { return PolyPair<Num>(p.coeff, unique(p.monom->replaceTerms(evaluatedArgs))); }

  };


  /** 
   * applies the rule
   */ 
  pair<Clause*,bool> applyRule(Clause* cl, bool doOrderingCheck) 
  {
    DEBUG("input clause: ", *cl);
    PowerMap powers;

    /* preprocessing. finds all products `X ⋅ X ⋅ ... ⋅ X` such that the rule is applicable */
    for (auto poly : iterPolynoms(cl)) {
      poly.apply(Preprocess { powers, });
    }

    bool applicable = 
      iterTraits(powers.iter())
        .find([](PowerMap::Entry& e) { return !e.value().isBot() && e.value().unwrap() >= 3; })
        .isSome();

    DEBUG("generalizations: ", powers);

    if (applicable) {
      return generalizeBottomUp(cl, EvaluateMonom<Generalize> { Generalize { powers, doOrderingCheck } });
    } else {
      return nop(cl);
    }
  }

  
};

pair<Clause*,bool> VariableMultiplicationGeneralization::simplify(Clause* cl, bool doOrderingCheck) 
{ 
  CALL("VariableMultiplicationGeneralization::simplify")
  return Rule3::applyRule(cl, doOrderingCheck);
}

VariableMultiplicationGeneralization::~VariableMultiplicationGeneralization()  { }


pair<Clause*,bool> VariablePowerGeneralization::simplify(Clause* cl, bool doOrderingCheck) 
{ 
  CALL("VariablePowerGeneralization::simplify")
  return Rule4::applyRule(cl, doOrderingCheck);
}

VariablePowerGeneralization::~VariablePowerGeneralization()  {}

Stack<MaybeImmediateSimplification*> allArithmeticSubtermGeneralizations()
{ 
  return Stack<MaybeImmediateSimplification*> {
      new VariableMultiplicationGeneralization(),
      new VariablePowerGeneralization(),
      new NumeralMultiplicationGeneralization(),
      new AdditionGeneralization()
  };
}

} // Inferences
