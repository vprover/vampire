/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file SMTCheck.hpp
 * Routines for producing a ground SMT proof-check script
 */

#include <array>
#include <unordered_set>

#include "Debug/Assertion.hpp"
#include "Inferences/EqualityResolution.hpp"
#include "Inferences/Factoring.hpp"
#include "Inferences/Superposition.hpp"
#include "Kernel/Theory.hpp"
#include "Lib/Exception.hpp"
#include "SMTCheck.hpp"

#include "Inferences/ALASCA/BinInf.hpp"
#include "Inferences/ALASCA/FourierMotzkin.hpp"
#include "Inferences/ALASCA/Superposition.hpp"
#include "Inferences/BinaryResolution.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Lib/SharedSet.hpp"
#include "Saturation/Splitter.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"

using namespace Kernel;
using Indexing::Splitter;
using SortMap = DHMap<unsigned, TermList>;

// get first N parents of a unit
template <unsigned N, typename T>
std::array<T *, N> getParents(T *unit)
{
  std::array<T *, N> parents;
  UnitIterator it = unit->getParents();
  for (unsigned i = 0; i < N; i++) {
    ALWAYS(it.hasNext())
    parents[i] = static_cast<T *>(it.next());
  }
  ALWAYS(!it.hasNext())
  return parents;
}

template<bool real>
struct SMTNumeral {
  const IntegerConstantType &constant;
};

template<bool real>
static std::ostream &operator<<(std::ostream &out, SMTNumeral<real> num) {
  if(num.constant.sign() == Sign::Neg)
    return out << "(- " << num.constant.abs() << (real ? ".0" : "") << ")";
  else
    return out << num.constant << (real ? ".0" : "");
}

struct Escaped {
  const char *name;
};

static std::ostream &operator<<(std::ostream &out, Escaped escaped) {
  out << "|_";
  for(const char *c = escaped.name; *c; c++)
    if(*c == '|')
      out << '#';
    else
      out << *c;
  return out << '|';
}

struct FunctionName {
  FunctionName(Signature::Symbol *symbol) : symbol(symbol) {}
  FunctionName(Term *t) : FunctionName(env.signature->getFunction(t->functor())) {}
  Signature::Symbol *symbol;
};

static std::ostream &operator<<(std::ostream &out, FunctionName name) {
  auto f = name.symbol;
  if(!f->interpreted())
    return out << Escaped {f->name().c_str()};
  if(f->integerConstant())
    return out << SMTNumeral<false> {f->integerValue()};
  if(f->rationalConstant() || f->realConstant()) {
    auto rat = f->rationalConstant() ? f->rationalValue() : f->realValue();
    return out << "(/ " << SMTNumeral<true> {rat.numerator()} << ' ' << SMTNumeral<true> {rat.denominator()} << ")";
  }
  auto *interpreted = static_cast<Signature::InterpretedSymbol *>(f);
  switch(interpreted->getInterpretation()) {
  case Theory::EQUAL:
  case Theory::INT_IS_INT:
  case Theory::INT_IS_RAT:
  case Theory::INT_IS_REAL:
  case Theory::INT_GREATER:
  case Theory::INT_GREATER_EQUAL:
  case Theory::INT_LESS:
  case Theory::INT_LESS_EQUAL:
  case Theory::INT_DIVIDES:
  case Theory::RAT_IS_INT:
  case Theory::RAT_IS_RAT:
  case Theory::RAT_IS_REAL:
  case Theory::RAT_GREATER:
  case Theory::RAT_GREATER_EQUAL:
  case Theory::RAT_LESS:
  case Theory::RAT_LESS_EQUAL:
  case Theory::REAL_IS_INT:
  case Theory::REAL_IS_RAT:
  case Theory::REAL_IS_REAL:
  case Theory::REAL_GREATER:
  case Theory::REAL_GREATER_EQUAL:
  case Theory::REAL_LESS:
  case Theory::REAL_LESS_EQUAL:
    // should be predicates, not functions
    ASSERTION_VIOLATION
  case Theory::INT_SUCCESSOR:
    NOT_IMPLEMENTED;
  case Theory::INT_UNARY_MINUS:
  case Theory::RAT_UNARY_MINUS:
  case Theory::REAL_UNARY_MINUS:
    return out << '-';
  case Theory::INT_PLUS:
  case Theory::RAT_PLUS:
  case Theory::REAL_PLUS:
    return out << '+';
  case Theory::INT_MINUS:
  case Theory::RAT_MINUS:
  case Theory::REAL_MINUS:
    return out << '-';
  case Theory::INT_MULTIPLY:
  case Theory::RAT_MULTIPLY:
  case Theory::REAL_MULTIPLY:
    return out << '*';
  case Theory::INT_QUOTIENT_E:
  case Theory::RAT_QUOTIENT:
  case Theory::REAL_QUOTIENT:
    return out << '/';
  case Theory::INT_QUOTIENT_T:
  case Theory::INT_QUOTIENT_F:
  case Theory::RAT_QUOTIENT_E:
  case Theory::RAT_QUOTIENT_T:
  case Theory::RAT_QUOTIENT_F:
  case Theory::REAL_QUOTIENT_E:
  case Theory::REAL_QUOTIENT_T:
  case Theory::REAL_QUOTIENT_F:
    NOT_IMPLEMENTED;
  case Theory::INT_REMAINDER_E:
    return out << "mod";
  case Theory::INT_REMAINDER_T:
  case Theory::INT_REMAINDER_F:
  case Theory::RAT_REMAINDER_E:
  case Theory::RAT_REMAINDER_T:
  case Theory::RAT_REMAINDER_F:
  case Theory::REAL_REMAINDER_E:
  case Theory::REAL_REMAINDER_T:
  case Theory::REAL_REMAINDER_F:
    NOT_IMPLEMENTED;
  case Theory::INT_TRUNCATE:
  case Theory::RAT_TRUNCATE:
  case Theory::REAL_TRUNCATE:
    NOT_IMPLEMENTED;
  case Theory::INT_ROUND:
  case Theory::RAT_ROUND:
  case Theory::REAL_ROUND:
    NOT_IMPLEMENTED;
  case Theory::INT_ABS:
    NOT_IMPLEMENTED;
  case Theory::RAT_TO_INT:
  case Theory::REAL_TO_INT:
    return out << "to_int";
  case Theory::INT_TO_RAT:
  case Theory::INT_TO_REAL:
    return out << "to_real";
  // should be handled specially at the term level
  case Theory::INT_TO_INT:
  case Theory::RAT_TO_RAT:
  case Theory::RAT_TO_REAL:
  case Theory::REAL_TO_RAT:
  case Theory::REAL_TO_REAL:
  case Theory::RAT_FLOOR:
  case Theory::REAL_FLOOR:
  case Theory::RAT_CEILING:
  case Theory::REAL_CEILING:
    ASSERTION_VIOLATION
  // weird, not sure what these would do
  case Theory::INT_FLOOR:
  case Theory::INT_CEILING:
    ASSERTION_VIOLATION
  case Theory::ARRAY_SELECT:
  case Theory::ARRAY_BOOL_SELECT:
  case Theory::ARRAY_STORE:
    NOT_IMPLEMENTED;
  case Theory::INVALID_INTERPRETATION:
    ASSERTION_VIOLATION
  }
  return out;
}

struct PredicateName {
  PredicateName(Signature::Symbol *symbol) : symbol(symbol) {}
  PredicateName(Literal *l) : PredicateName(env.signature->getPredicate(l->functor())) {}
  Signature::Symbol *symbol;
};

static std::ostream &operator<<(std::ostream &out, PredicateName name) {
  auto p = name.symbol;
  if(!p->interpreted())
    return out << Escaped {p->name().c_str()};
  auto *interpreted = static_cast<Signature::InterpretedSymbol *>(p);
  switch(interpreted->getInterpretation()) {
  case Theory::EQUAL:
    return out << '=';
  case Theory::RAT_IS_INT:
  case Theory::REAL_IS_INT:
    return out << "is_int";
  case Theory::REAL_IS_RAT:
    return out << "is_rat";
  case Theory::INT_IS_INT:
  case Theory::INT_IS_RAT:
  case Theory::RAT_IS_RAT:
  case Theory::INT_IS_REAL:
  case Theory::RAT_IS_REAL:
  case Theory::REAL_IS_REAL:
    // should be special-cased at the term level
    ASSERTION_VIOLATION
  case Theory::INT_GREATER:
  case Theory::RAT_GREATER:
  case Theory::REAL_GREATER:
    return out << '>';
  case Theory::INT_GREATER_EQUAL:
  case Theory::RAT_GREATER_EQUAL:
  case Theory::REAL_GREATER_EQUAL:
    return out << ">=";
  case Theory::INT_LESS:
  case Theory::RAT_LESS:
  case Theory::REAL_LESS:
    return out << '<';
  case Theory::INT_LESS_EQUAL:
  case Theory::RAT_LESS_EQUAL:
  case Theory::REAL_LESS_EQUAL:
    return out << "<=";
  case Theory::INT_DIVIDES:
    NOT_IMPLEMENTED;

  case Theory::INT_SUCCESSOR:
  case Theory::INT_UNARY_MINUS:
  case Theory::INT_PLUS:
  case Theory::INT_MINUS:
  case Theory::INT_MULTIPLY:
  case Theory::INT_QUOTIENT_E:
  case Theory::INT_QUOTIENT_T:
  case Theory::INT_QUOTIENT_F:
  case Theory::INT_REMAINDER_E:
  case Theory::INT_REMAINDER_T:
  case Theory::INT_REMAINDER_F:
  case Theory::INT_FLOOR:
  case Theory::INT_CEILING:
  case Theory::INT_TRUNCATE:
  case Theory::INT_ROUND:
  case Theory::INT_ABS:
  case Theory::RAT_UNARY_MINUS:
  case Theory::RAT_PLUS:
  case Theory::RAT_MINUS:
  case Theory::RAT_MULTIPLY:
  case Theory::RAT_QUOTIENT:
  case Theory::RAT_QUOTIENT_E:
  case Theory::RAT_QUOTIENT_T:
  case Theory::RAT_QUOTIENT_F:
  case Theory::RAT_REMAINDER_E:
  case Theory::RAT_REMAINDER_T:
  case Theory::RAT_REMAINDER_F:
  case Theory::RAT_FLOOR:
  case Theory::RAT_CEILING:
  case Theory::RAT_TRUNCATE:
  case Theory::RAT_ROUND:
  case Theory::REAL_UNARY_MINUS:
  case Theory::REAL_PLUS:
  case Theory::REAL_MINUS:
  case Theory::REAL_MULTIPLY:
  case Theory::REAL_QUOTIENT:
  case Theory::REAL_QUOTIENT_E:
  case Theory::REAL_QUOTIENT_T:
  case Theory::REAL_QUOTIENT_F:
  case Theory::REAL_REMAINDER_E:
  case Theory::REAL_REMAINDER_T:
  case Theory::REAL_REMAINDER_F:
  case Theory::REAL_FLOOR:
  case Theory::REAL_CEILING:
  case Theory::REAL_TRUNCATE:
  case Theory::REAL_ROUND:
  case Theory::INT_TO_INT:
  case Theory::INT_TO_RAT:
  case Theory::INT_TO_REAL:
  case Theory::RAT_TO_INT:
  case Theory::RAT_TO_RAT:
  case Theory::RAT_TO_REAL:
  case Theory::REAL_TO_INT:
  case Theory::REAL_TO_RAT:
  case Theory::REAL_TO_REAL:
  case Theory::ARRAY_SELECT:
  case Theory::ARRAY_BOOL_SELECT:
  case Theory::ARRAY_STORE:
    // should be predicates, not functions
    ASSERTION_VIOLATION
  case Theory::INVALID_INTERPRETATION:
    ASSERTION_VIOLATION
  }
  return out;
}

struct Blank {};
static std::ostream &operator<<(std::ostream &out, Blank) { return out; }
struct Inhabit {};
static std::ostream &operator<<(std::ostream &out, Inhabit) { return out << "inhabit_"; }

template<typename Prefix = Blank>
struct SortName {
  SortName(unsigned functor) : functor(functor) {}
  SortName(AtomicSort *s) : functor(s->functor()) {}
  unsigned functor;
};

template<typename Prefix>
static std::ostream &operator<<(std::ostream &out, SortName<Prefix> name) {
  Prefix prefix;
  switch(name.functor) {
  case Signature::DEFAULT_SORT_CON:
    return out << prefix << "iota";
  case Signature::BOOL_SRT_CON:
    return out << prefix << "Bool";
  case Signature::INTEGER_SRT_CON:
    return out << prefix << "Int";
  // SMT-LIB doesn't have rationals
  case Signature::RATIONAL_SRT_CON:
  case Signature::REAL_SRT_CON:
    return out << prefix << "Real";
  }
  return out << '|' << prefix << '_' << env.signature->getTypeCon(name.functor)->name() << '|';
}

struct Args {
  TermList *start;
  SortMap &conclSorts;
  SortMap &otherSorts;
};

static std::ostream &operator<<(std::ostream &out, Args args)
{
  if (args.start->isEmpty())
    return out;

  Stack<TermList *> todo;
  TermList empty;
  TermList *current = args.start;
  while (true) {
    out << " ";
    if (current->isVar()) {
      unsigned var = current->var();
      if (args.conclSorts.findPtr(var))
        out << "v" << var;
      else
        out << SortName<Inhabit>(static_cast<AtomicSort *>(args.otherSorts.get(var).term()));
      current = current->next();
    }
    else if (current->isTerm()) {
      Term *term = current->term();
      FunctionName name(term);
      if (term->arity()) {
        if(name.symbol->interpreted()) {
          auto interpreted = static_cast<Signature::InterpretedSymbol *>(name.symbol);
          switch(interpreted->getInterpretation()) {
          // identity functions, skip
          case Theory::INT_TO_INT:
          case Theory::RAT_TO_RAT:
          case Theory::RAT_TO_REAL:
          case Theory::REAL_TO_RAT:
          case Theory::REAL_TO_REAL:
            // these do nothing in SMT-LIB, skip them by 'forgetting' there is a function here
            // disgusting hack: use recursion to break the paren-closing invariant,
            out << Args { term->args(), args.conclSorts, args.otherSorts };
            // treat `current` like a variable,
            current = current->next();
            // and go to the part where we check the rest of the arguments
            goto carry_on;
          // polyfill with compound term
          case Theory::RAT_FLOOR:
          case Theory::REAL_FLOOR:
            out << "(to_real (to_int";
            todo.push(current->next());
            // extra close-paren
            todo.push(&empty);
            break;
          case Theory::RAT_CEILING:
          case Theory::REAL_CEILING:
            out << "(- (to_real (to_int (-";
            todo.push(current->next());
            // extra close-parens
            todo.push(&empty);
            todo.push(&empty);
            todo.push(&empty);
            break;
          default:
            out << "(" << name;
            todo.push(current->next());
            break;
          }
        }
        else if(name.symbol->linMul()) {
          out << "(* ";
          if(auto attempt = env.signature->tryLinMul<IntegerConstantType>(term->functor()); attempt.isSome()) {
            auto factor = SMTNumeral<false> {attempt.unwrap()};
            out << factor;
          }
          else if(auto attempt = env.signature->tryLinMul<RationalConstantType>(term->functor()); attempt.isSome()) {
            auto factor = attempt.unwrap();
            out << "(/ " << SMTNumeral<true> {factor.numerator()} << " " << SMTNumeral<true> {factor.denominator()} << ")";
          }
          else if(auto attempt = env.signature->tryLinMul<RealConstantType>(term->functor()); attempt.isSome()) {
            auto factor = attempt.unwrap();
            out << "(/ " << SMTNumeral<true> {factor.numerator()} << " " << SMTNumeral<true> {factor.denominator()} << ")";
          }
          else
            ASSERTION_VIOLATION
          todo.push(current->next());
        }
        else {
          out << "(" << name;
          todo.push(current->next());
        }
        current = term->args();
      }
      else {
        if(env.signature->isFoolConstantSymbol(false, term->functor()))
          out << "false";
        else if(env.signature->isFoolConstantSymbol(true, term->functor()))
          out << "true";
        else
          out << name;
        current = current->next();
      }
    }

carry_on:
    while (current->isEmpty()) {
      if (todo.isEmpty())
        return out;

      current = todo.pop();
      out << ")";
    }
  }
}

struct Lit {
  Literal *literal;
  SortMap &conclSorts;
  SortMap &otherSorts;
};

static std::ostream &operator<<(std::ostream &out, Lit lit)
{
  Literal *literal = lit.literal;
  PredicateName name(literal);
  if (!literal->polarity())
    out << "(not ";
  if (literal->arity())
    out << "(";

  if(name.symbol->interpreted()) {
    auto interpreted = static_cast<Signature::InterpretedSymbol *>(name.symbol);
    switch(interpreted->getInterpretation()) {
    case Theory::INT_IS_INT:
    case Theory::INT_IS_RAT:
    case Theory::INT_IS_REAL:
    case Theory::RAT_IS_RAT:
    case Theory::RAT_IS_REAL:
    case Theory::REAL_IS_REAL:
      out << "true";
      goto finish;
    default:
      break;
    }
  }
  out << name << Args{literal->args(), lit.conclSorts, lit.otherSorts};
  if (literal->arity())
    out << ")";

finish:
  if (!literal->polarity())
    out << ")";
  return out;
}

struct Sort {
  TermList sort;
};

static std::ostream &operator<<(std::ostream &out, Sort print) {
  AtomicSort *sort = static_cast<AtomicSort *>(print.sort.term());
  // don't support type constructors yet
  ASS_EQ(sort->arity(), 0)
  return out << SortName(sort);
}


template <bool flip = false>
struct Split {
  unsigned level;
  Split(unsigned level) : level(level) {}
};

template <bool flip>
static std::ostream &operator<<(std::ostream &out, Split<flip> split)
{
  SATLiteral sat = Splitter::getLiteralFromName(split.level);
  return out
      << (flip == sat.positive() ? "(not " : "")
      << "sp" << sat.var()
      << (flip == sat.positive() ? ")" : "");
}

struct Identity {
  Literal *operator()(Literal *l) { return l; }
};

struct DoSubst {
  Substitution &subst;
  DoSubst(Substitution &subst) : subst(subst) {}
  Literal *operator()(Literal *l) { return SubstHelper::apply(l, subst); }
};

template <unsigned bank>
struct DoRobSubst {
  const RobSubstitution &subst;
  DoRobSubst(const RobSubstitution &subst) : subst(subst) {}
  Literal *operator()(Literal *l) { return subst.apply(l, bank); }
};

template <typename Transform = Identity>
static void outputPremise(std::ostream &out, SortMap &conclSorts, Clause *cl, Transform transform = Transform{})
{
  out << "(assert (or";
  for (Literal *l : *cl) {
    l = transform(l);
    SortMap otherSorts;
    SortHelper::collectVariableSorts(l, otherSorts);
    out << " " << Lit{l, conclSorts, otherSorts};
  }
  if (cl->splits()) {
    SplitSet &clSplits = *cl->splits();
    for (unsigned i = 0; i < clSplits.size(); i++) {
      out << " " << Split<true>(clSplits[i]);
    }
  }
  out << "))\n";
}

static void outputConclusion(std::ostream &out, SortMap &conclSorts, Clause *cl)
{
  SortMap otherSorts;
  for (Literal *l : *cl)
    out << "(assert " << Lit{Literal::complementaryLiteral(l), conclSorts, otherSorts} << ")\n";

  if (cl->splits()) {
    SplitSet &clSplits = *cl->splits();
    for (unsigned i = 0; i < clSplits.size(); i++)
      out << "(assert " << Split(clSplits[i]) << ")\n";
  }
}

static void trivial(std::ostream &out, SortMap &conclSorts, Clause *concl)
{
  UnitIterator parents = concl->getParents();
  while (parents.hasNext()) {
    Unit *parent = parents.next();
    ASS(parent->isClause())
    outputPremise(out, conclSorts, parent->asClause());
  }
  outputConclusion(out, conclSorts, concl->asClause());
}

static void resolution(std::ostream &out, SortMap &conclSorts, Clause *concl)
{
  auto [left, right] = getParents<2>(concl);
  const auto &br = env.proofExtra.get<Inferences::BinaryResolutionExtra>(concl);

  auto uwa = AbstractingUnifier::empty(AbstractionOracle(env.options->unificationWithAbstraction()));
  Literal *selectedLeft = br.selectedLiteral.selectedLiteral;
  Literal *selectedRight = br.otherLiteral;
  for(unsigned i = 0; i < selectedLeft->arity(); i++)
    ALWAYS(uwa.unify((*selectedLeft)[i], 0, (*selectedRight)[i], 1))
  ASS_NEQ(selectedLeft->polarity(), selectedRight->polarity())
  RobSubstitution &subst = uwa.subs();

  for (unsigned i = 0; i < left->length(); i++)
    if ((*left)[i] != selectedLeft)
      subst.apply((*left)[i], 0);
  for (unsigned i = 0; i < right->length(); i++)
    if ((*right)[i] != selectedRight)
      subst.apply((*right)[i], 1);

  outputPremise(out, conclSorts, left->asClause(), DoRobSubst<0>(subst));
  outputPremise(out, conclSorts, right->asClause(), DoRobSubst<1>(subst));
  outputConclusion(out, conclSorts, concl->asClause());
}

static void subsumptionResolution(std::ostream &out, SortMap &conclSorts, Clause *concl)
{
  auto [left, right] = getParents<2>(concl);
  auto sr = env.proofExtra.get<Inferences::LiteralInferenceExtra>(concl);
  Literal *m = sr.selectedLiteral;

  // reconstruct match by calling into the SATSR code
  SATSubsumption::SATSubsumptionAndResolution satSR;
  ALWAYS(satSR.checkSubsumptionResolutionWithLiteral(right, left, left->getLiteralPosition(m)))
  auto subst = satSR.getBindingsForSubsumptionResolutionWithLiteral();

  outputPremise(out, conclSorts, left->asClause());
  outputPremise(out, conclSorts, right->asClause(), DoSubst(subst));
  outputConclusion(out, conclSorts, concl->asClause());
}

static void factoring(std::ostream &out, SortMap &conclSorts, Clause *concl) {
  auto [premise] = getParents<1>(concl);
  const auto &fact = env.proofExtra.get<Inferences::FactoringExtra>(concl);

  RobSubstitution subst;
  Literal *selected = fact.selectedLiteral.selectedLiteral;
  Literal *other = fact.otherLiteral;
  ASS_EQ(selected->polarity(), other->polarity())
  ASS_EQ(selected->functor(), other->functor())
  ALWAYS(subst.unify(TermList(selected), 0, TermList(other), 0));

  for (unsigned i = 0; i < premise->length(); i++)
    if ((*premise)[i] != other)
      subst.apply((*premise)[i], 0);

  outputPremise(out, conclSorts, premise->asClause(), DoRobSubst<0>(subst));
  outputConclusion(out, conclSorts, concl->asClause());
}

static void equalityResolution(std::ostream &out, SortMap &conclSorts, Clause *concl) {
  auto [premise] = getParents<1>(concl);
  const auto &res = env.proofExtra.get<Inferences::EqualityResolutionExtra>(concl);

  RobSubstitution subst;
  Literal *selected = res.selectedLiteral;
  ASS(selected->isEquality())
  ASS(selected->isNegative())
  TermList s = selected->termArg(0), t = selected->termArg(1);
  ALWAYS(subst.unify(s, 0, t, 0));
  for (unsigned i = 0; i < premise->length(); i++)
    if ((*premise)[i] != selected)
      subst.apply((*premise)[i], 0);

  outputPremise(out, conclSorts, premise->asClause(), DoRobSubst<0>(subst));
  outputConclusion(out, conclSorts, concl->asClause());
}

static void superposition(std::ostream &out, SortMap &conclSorts, Clause *concl)
{
  auto [left, right] = getParents<2>(concl);
  auto sup = env.proofExtra.get<Inferences::SuperpositionExtra>(concl);

  // compute unifier for selected literals
  RobSubstitution subst;
  Literal *leftSelected = sup.selected.selectedLiteral.selectedLiteral;
  Literal *rightSelected = sup.selected.otherLiteral;
  TermList from = sup.rewrite.lhs;
  TermList to = EqHelper::getOtherEqualitySide(rightSelected, from);
  TermList target = sup.rewrite.rewritten;
  ASS(rightSelected->isEquality())
  ASS(rightSelected->isPositive())
  ASS(rightSelected->termArg(0) == from || rightSelected->termArg(1) == from)
  ALWAYS(subst.unify(target, 0, from, 1))

  subst.apply(to, 1);
  subst.apply(leftSelected, 0);
  subst.apply(target, 0);
  subst.apply(from, 1);
  for (unsigned i = 0; i < left->length(); i++)
    if ((*left)[i] != leftSelected)
      subst.apply((*left)[i], 0);
  for (unsigned i = 0; i < right->length(); i++)
    if ((*right)[i] != rightSelected)
      subst.apply((*right)[i], 1);

  outputPremise(out, conclSorts, left->asClause(), DoRobSubst<0>(subst));
  outputPremise(out, conclSorts, right->asClause(), DoRobSubst<1>(subst));
  outputConclusion(out, conclSorts, concl->asClause());
}

// check whether `demodulator` l = r rewrites left-to-right in the context of C[t] -> C[s]
// TODO copied from Dedukti, merge at some point
static bool isL2RDemodulatorFor(Literal *demodulator, Clause *rewritten, TermList target, Clause *result)
{
  ASS(demodulator->isEquality())
  ASS(demodulator->isPositive())

  // TODO this is waaay overkill, but it's very hard to work out which way a demodulator was used
  // consult MH about how best to do this
  Substitution subst;
  if (!MatchingUtils::matchTerms(demodulator->termArg(0), target, subst))
    return false;
  TermList rhsSubst = SubstHelper::apply(demodulator->termArg(1), subst);

  for (Literal *l : rewritten->iterLits())
    if (!result->contains(l) && !result->contains(EqHelper::replace(l, target, rhsSubst)))
      return false;

  return true;
}

static void demodulation(std::ostream &out, SortMap &conclSorts, Clause *concl)
{
  auto [left, right] = getParents<2>(concl);
  auto rw = env.proofExtra.get<Inferences::RewriteInferenceExtra>(concl);

  Substitution subst;
  Literal *rightLit = (*right)[0];
  TermList target = rw.rewritten;
  TermList from = rightLit->termArg(!isL2RDemodulatorFor(rightLit, left, target, concl));
  ASS(rightLit->isEquality())
  ASS(rightLit->isPositive())
  ASS(rightLit->termArg(0) == from || rightLit->termArg(1) == from)
  ALWAYS(MatchingUtils::matchTerms(from, target, subst))

  outputPremise(out, conclSorts, left->asClause());
  outputPremise(out, conclSorts, right->asClause(), DoSubst(subst));
  outputConclusion(out, conclSorts, concl->asClause());
}

static void splitClause(std::ostream &out, SortMap &conclSorts, Unit *concl)
{
  ASS(conclSorts.isEmpty())

  SATClause *sat = env.proofExtra.get<Indexing::SATClauseExtra>(concl).clause;
  std::unordered_set<unsigned> seen;
  for(SATLiteral l : sat->iter())
    if(seen.insert(l.var()).second)
      out << "(declare-const sp" << l.var() << " Bool)\n";

  auto parents = concl->getParents();
  ALWAYS(parents.hasNext())
  Clause *split = parents.next()->asClause();
  outputPremise(out, conclSorts, split);
  for (Unit *u : iterTraits(parents)) {
    Clause *component = env.proofExtra.get<Indexing::SplitDefinitionExtra>(u).component;
    SortMap otherSorts;
    SortHelper::collectVariableSorts(component, otherSorts);
    out << "(assert (= " << Split {component->splits()->sval()} << " (or";
    for(Literal *l : *component)
      out << ' ' << Lit {l, conclSorts, otherSorts};
    out << ")))\n";
  }

  for(SATLiteral l : sat->iter())
    out
      << "(assert "
      << (l.positive() ? "(not " : "")
      << "sp" << l.var()
      << (l.positive() ? ")" : "")
      << ")\n";
}

static void satRefutation(std::ostream &out, SortMap &conclSorts, Unit *concl) {
  std::unordered_set<unsigned> seen;
  for(Unit *u : iterTraits(concl->getParents()))
    for(SATLiteral l : env.proofExtra.get<Indexing::SATClauseExtra>(u).clause->iter())
      if(seen.insert(l.var()).second)
        out << "(declare-const sp" << l.var() << " Bool)\n";

  for(Unit *u : iterTraits(concl->getParents())) {
    out << "(assert (or";
    for(SATLiteral l : env.proofExtra.get<Indexing::SATClauseExtra>(u).clause->iter())
      out
        << ' ' << (l.positive() ? "" : "(not ")
        << "sp" << l.var()
        << (l.positive() ? "" : ")");
    out << "))\n";
  }
}

template<class Rule>
static void alascaBinInf(std::ostream &out, SortMap &conclSorts, Clause *concl) {
  auto [left, right] = getParents<2>(concl);
  const auto &fm = env.proofExtra.get<ALASCA::BinInfExtra<Rule>>(concl);

  auto uwa = AbstractingUnifier::empty(AbstractionOracle(env.options->unificationWithAbstraction()));
  ALWAYS(uwa.unify(fm.left.key(), 0, fm.right.key(), 1))
  RobSubstitution &subst = uwa.subs();

  subst.apply(fm.left.literal(), 0);
  subst.apply(fm.right.literal(), 1);
  for (unsigned i = 0; i < left->length(); i++)
    subst.apply((*left)[i], 0);
  for (unsigned i = 0; i < right->length(); i++)
    subst.apply((*right)[i], 1);

  outputPremise(out, conclSorts, left->asClause(), DoRobSubst<0>(subst));
  outputPremise(out, conclSorts, right->asClause(), DoRobSubst<1>(subst));
  outputConclusion(out, conclSorts, concl->asClause());
}

static SortMap outputSkolemsAndGetSorts(std::ostream &out, Unit *u)
{
  SortMap sorts;
  SortHelper::collectVariableSorts(u, sorts);
  auto it = sorts.items();
  while (it.hasNext()) {
    auto [var, sort] = it.next();
    out << "(declare-const v" << var << " " << Sort {sort} << ")\n";
  }
  return sorts;
}

static void outputSplits(std::ostream &out, Unit *u)
{
  if (!u->isClause())
    return;
  Clause *cl = u->asClause();
  if (!cl->splits())
    return;
  SplitSet &clSplits = *cl->splits();

  std::unordered_set<unsigned> splits;
  for (unsigned i = 0; i < clSplits.size(); i++)
    splits.insert(clSplits[i]);

  UnitIterator parents = u->getParents();
  while (parents.hasNext()) {
    Unit *parent = parents.next();
    if (!parent->isClause())
      continue;
    Clause *cl = parent->asClause();
    if (!cl->splits())
      continue;
    SplitSet &clSplits = *cl->splits();
    for (unsigned i = 0; i < clSplits.size(); i++)
      splits.insert(clSplits[i]);
  }

  for (unsigned split : splits)
    out << "(declare-const sp" << Splitter::getLiteralFromName(split).var() << " Bool)\n";
}

namespace Shell {
namespace SMTCheck {

void outputSignature(std::ostream &out)
{
  out << "(set-logic ALL)\n";
  out << "(declare-sort iota 0)\n";
  out << "(declare-const inhabit_iota iota)\n";
  out << "(declare-const inhabit_Int Int)\n";
  out << "(declare-const inhabit_Real Real)\n";
  // bit cursed but OK
  out << "(declare-const inhabit_Bool Bool)\n";
  out << "(declare-fun is_rat (Real) Bool)\n";

  Signature &sig = *env.signature;
  for(unsigned i = Signature::FIRST_USER_CON; i < sig.typeCons(); i++) {
    out << "(declare-sort " << SortName(i);
#if VDEBUG
    Signature::Symbol *type = sig.getTypeCon(i);
    OperatorType *typeType = type->typeConType();
    // we don't support polymorphism yet
    ASS_EQ(typeType->numTypeArguments(), 0)
#endif
    out << " 0)\n";
    out << "(declare-const " << SortName<Inhabit>(i) << ' ' << SortName(i) << ")\n";
  }

  for(unsigned i = 0; i < sig.functions(); i++) {
    Signature::Symbol *fun = sig.getFunction(i);
    if(fun->interpreted() || fun->linMul())
      continue;

    out << "(declare-fun " << FunctionName(fun);
    OperatorType *type = fun->fnType();
    TermList range = type->result();

    // we don't support polymorphism yet
    ASS_EQ(type->numTypeArguments(), 0)
    out << " (";
    for (unsigned i = 0; i < type->arity(); i++)
      out << (i == 0 ? "" : " ") << Sort {type->arg(i)};
    out << ") " << Sort {range} << ")\n";
  }

  for(unsigned i = 1; i < sig.predicates(); i++) {
    Signature::Symbol *pred = sig.getPredicate(i);
    if(pred->interpreted())
      continue;

    out << "(declare-fun " << PredicateName(pred);
    OperatorType *type = pred->predType();

    // we don't support polymorphism yet
    ASS_EQ(type->numTypeArguments(), 0)
    out << " (";
    for (unsigned i = 0; i < type->arity(); i++)
      out << (i == 0 ? "" : " ") << Sort {type->arg(i)};
    out << ") Bool)\n";
  }
}

void outputStep(std::ostream &out, Unit *u)
{
  InferenceRule rule = u->inference().rule();
  if (
      // can't check the input
      rule == InferenceRule::INPUT || rule == InferenceRule::NEGATED_CONJECTURE
      // can't check skolem symbol introduction
      || rule == InferenceRule::SKOLEM_SYMBOL_INTRODUCTION
      // can't check distinctness axioms
      || rule == InferenceRule::DISTINCTNESS_AXIOM
      // can't check definition introduction
      || rule == InferenceRule::AVATAR_DEFINITION || rule == InferenceRule::AVATAR_COMPONENT
      // nothing to check here
      || rule == InferenceRule::AVATAR_CONTRADICTION_CLAUSE)
    return;

  out << "\n; step " << u->number() << "\n";
  out << "(push)\n";

  bool sorry = false;
  auto conclSorts = outputSkolemsAndGetSorts(out, u);
  outputSplits(out, u);
  switch (rule) {
    case InferenceRule::REMOVE_DUPLICATE_LITERALS:
    case InferenceRule::TRIVIAL_INEQUALITY_REMOVAL:
    case InferenceRule::EVALUATION:
    case InferenceRule::ALASCA_NORMALIZATION:
    //TODO below are trivial but would have to (declare-datatypes ...)
    //case InferenceRule::TERM_ALGEBRA_DISTINCTNESS:
    //case InferenceRule::TERM_ALGEBRA_INJECTIVITY_SIMPLIFYING:
    //case InferenceRule::TERM_ALGEBRA_INJECTIVITY_GENERATING:
    case InferenceRule::THA_COMMUTATIVITY:
    case InferenceRule::THA_ASSOCIATIVITY:
    case InferenceRule::THA_RIGHT_IDENTITY:
    case InferenceRule::THA_LEFT_IDENTITY:
    case InferenceRule::THA_INVERSE_OP_OP_INVERSES:
    case InferenceRule::THA_INVERSE_OP_UNIT:
    case InferenceRule::THA_INVERSE_ASSOC:
    case InferenceRule::THA_NONREFLEX:
    case InferenceRule::THA_TRANSITIVITY:
    case InferenceRule::THA_ORDER_TOTALITY:
    case InferenceRule::THA_ORDER_MONOTONICITY:
    case InferenceRule::THA_ALASCA:
    case InferenceRule::THA_PLUS_ONE_GREATER:
    case InferenceRule::THA_ORDER_PLUS_ONE_DICHOTOMY:
    case InferenceRule::THA_MINUS_MINUS_X:
    case InferenceRule::THA_TIMES_ZERO:
    case InferenceRule::THA_DISTRIBUTIVITY:
    case InferenceRule::THA_DIVISIBILITY:
    case InferenceRule::THA_MODULO_MULTIPLY:
    case InferenceRule::THA_MODULO_POSITIVE:
    case InferenceRule::THA_MODULO_SMALL:
    case InferenceRule::THA_DIVIDES_MULTIPLY:
    case InferenceRule::THA_NONDIVIDES_SKOLEM:
    case InferenceRule::THA_ABS_EQUALS:
    case InferenceRule::THA_ABS_MINUS_EQUALS:
    case InferenceRule::THA_QUOTIENT_NON_ZERO:
    case InferenceRule::THA_QUOTIENT_MULTIPLY:
    case InferenceRule::THA_EXTRA_INTEGER_ORDERING:
    case InferenceRule::THA_FLOOR_SMALL:
    case InferenceRule::THA_FLOOR_BIG:
    case InferenceRule::THA_CEILING_BIG:
    case InferenceRule::THA_CEILING_SMALL:
    case InferenceRule::THA_TRUNC1:
    case InferenceRule::THA_TRUNC2:
    case InferenceRule::THA_TRUNC3:
    case InferenceRule::THA_TRUNC4:
    case InferenceRule::THA_ARRAY_EXTENSIONALITY:
    case InferenceRule::THA_BOOLEAN_ARRAY_EXTENSIONALITY:
    case InferenceRule::THA_BOOLEAN_ARRAY_WRITE1:
    case InferenceRule::THA_BOOLEAN_ARRAY_WRITE2:
    case InferenceRule::THA_ARRAY_WRITE1:
    case InferenceRule::THA_ARRAY_WRITE2:
    case InferenceRule::TERM_ALGEBRA_ACYCLICITY_AXIOM:
    case InferenceRule::TERM_ALGEBRA_DIRECT_SUBTERMS_AXIOM:
    case InferenceRule::TERM_ALGEBRA_SUBTERMS_TRANSITIVE_AXIOM:
    case InferenceRule::TERM_ALGEBRA_DISCRIMINATION_AXIOM:
    case InferenceRule::TERM_ALGEBRA_DISTINCTNESS_AXIOM:
    case InferenceRule::TERM_ALGEBRA_EXHAUSTIVENESS_AXIOM:
    case InferenceRule::TERM_ALGEBRA_INJECTIVITY_AXIOM:
    case InferenceRule::FOOL_AXIOM_TRUE_NEQ_FALSE:
    case InferenceRule::FOOL_AXIOM_ALL_IS_TRUE_OR_FALSE:
      trivial(out, conclSorts, u->asClause());
      break;
    case InferenceRule::RESOLUTION:
      resolution(out, conclSorts, u->asClause());
      break;
    case InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION:
    case InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION:
      subsumptionResolution(out, conclSorts, u->asClause());
      break;
    case InferenceRule::FACTORING:
      factoring(out, conclSorts, u->asClause());
      break;
    case InferenceRule::EQUALITY_RESOLUTION:
      equalityResolution(out, conclSorts, u->asClause());
      break;
    case InferenceRule::SUPERPOSITION:
      superposition(out, conclSorts, u->asClause());
      break;
    case InferenceRule::FORWARD_DEMODULATION:
    case InferenceRule::BACKWARD_DEMODULATION:
      demodulation(out, conclSorts, u->asClause());
      break;
    case InferenceRule::AVATAR_SPLIT_CLAUSE:
      splitClause(out, conclSorts, u);
      break;
    case InferenceRule::AVATAR_REFUTATION:
      satRefutation(out, conclSorts, u);
      break;
    case InferenceRule::ALASCA_FOURIER_MOTZKIN:
      alascaBinInf<ALASCA::FourierMotzkinConf>(out, conclSorts, u->asClause());
      break;
    case InferenceRule::ALASCA_SUPERPOSITION:
      alascaBinInf<ALASCA::SuperpositionConf>(out, conclSorts, u->asClause());
      break;
    default:
      sorry = true;
      out << "(echo \"sorry: " << ruleName(rule) << "\")\n";
  }
  if (!sorry) {
    out << "(set-info :status unsat)\n";
    out << "(check-sat)\n";
  }
  out << "(pop)\n";
}

} // namespace SMTCheck
} // namespace Shell
