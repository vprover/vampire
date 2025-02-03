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

#include <unordered_set>

#include "Inferences/Superposition.hpp"
#include "SMTCheck.hpp"

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
template<unsigned N, typename T>
std::array<T *, N> getParents(T *unit) {
  std::array<T *, N> parents;
  UnitIterator it = unit->getParents();
  for(unsigned i = 0; i < N; i++) {
    ALWAYS(it.hasNext())
    parents[i] = static_cast<T *>(it.next());
  }
  ALWAYS(!it.hasNext())
  return parents;
}

struct Name {
  std::string_view name;
  Name(std::string_view name) : name(name) {}
};

static std::ostream &operator<<(std::ostream &out, Name name) {
  return out << '|' << name.name << '|';
}

struct Args {
  TermList *start;
  SortMap &conclSorts;
};

static std::ostream &operator<<(std::ostream &out, Args args) {
  if(args.start->isEmpty())
    return out;

  Stack<TermList *> todo;
  TermList *current = args.start;
  while(true) {
    out << " ";
    if(current->isVar()) {
      unsigned var = current->var();
      if(args.conclSorts.findPtr(var))
        out << "v" << var;
      else
        out << "inhabit";
      current = current->next();
    }
    else if(current->isTerm()) {
      Term *term = current->term();
      if(term->arity()) {
        out << "(" << Name(term->functionName());
        todo.push(current->next());
        current = term->args();
      }
      else {
        out << Name(term->functionName());
        current = current->next();
      }
    }

    while(current->isEmpty()) {
      if(todo.isEmpty())
        return out;

      current = todo.pop();
      out << ")";
    }
  }
}

struct Lit {
  Literal *literal;
  SortMap &conclSorts;
};

static std::ostream &operator<<(std::ostream &out, Lit lit) {
  Literal *literal = lit.literal;
  if(!literal->polarity())
    out << "(not ";
  if(literal->arity())
    out << "(";
  out << Name(literal->predicateName()) << Args {literal->args(), lit.conclSorts};
  if(literal->arity())
    out << ")";
  if(!literal->polarity())
    out << ")";
  return out;
}

template<bool flip = false>
struct Split {
  unsigned level;
  Split(unsigned level) : level(level) {}
};

template<bool flip>
static std::ostream &operator<<(std::ostream &out, Split<flip> split) {
  SATLiteral sat = Splitter::getLiteralFromName(split.level);
  return out
    << (flip == sat.polarity() ? "(not " : "")
    << "sp" << sat.var()
    << (flip == sat.polarity() ? ")" : "");
}

struct Identity {
  Literal *operator()(Literal *l) { return l; }
};

struct DoSimpleSubst {
  SimpleSubstitution &subst;
  DoSimpleSubst(SimpleSubstitution &subst) : subst(subst) {}
  Literal *operator()(Literal *l) { return SubstHelper::apply(l, subst); }
};

template<unsigned bank>
struct DoRobSubst {
  const RobSubstitution &subst;
  DoRobSubst(const RobSubstitution &subst) : subst(subst) {}
  Literal *operator()(Literal *l) { return subst.apply(l, bank); }
};

template<typename Transform>
static void outputPremise(std::ostream &out, SortMap &conclSorts, Clause *cl, Transform transform) {
  out << "(assert (or";
  for(Literal *l : *cl) {
    out << " " << Lit {transform(l), conclSorts};
  }
  if(cl->splits()) {
    SplitSet &clSplits = *cl->splits();
    for(unsigned i = 0; i < clSplits.size(); i++) {
      out << " " << Split(clSplits[i]);
    }
  }
  out << "))\n";
}

static void outputPremise(std::ostream &out, SortMap &conclSorts, Clause *cl) {
  outputPremise(out, conclSorts, cl, Identity());
}

static void outputConclusion(std::ostream &out, SortMap &conclSorts, Clause *cl) {
  for(Literal *l : *cl)
    out << "(assert " << Lit {Literal::complementaryLiteral(l), conclSorts} << ")\n";

  if(cl->splits()) {
    SplitSet &clSplits = *cl->splits();
    for(unsigned i = 0; i < clSplits.size(); i++)
      out << "(assert " << Split<true>(clSplits[i]) << ")\n";
  }
}

static SortMap outputSkolemsAndGetSorts(std::ostream &out, Unit *u) {
  DHMap<unsigned, TermList> sorts;
  SortHelper::collectVariableSorts(u, sorts);
  auto it = sorts.items();
  while(it.hasNext()) {
    auto [var, sort] = it.next();
    ASS_EQ(sort, AtomicSort::defaultSort())
    out << "(declare-const v" << var << " I)\n";
  }
  return sorts;
}

static void outputSplits(std::ostream &out, Unit *u) {
  if(!u->isClause())
    return;
  Clause *cl = u->asClause();
  if(!cl->splits())
    return;
  SplitSet &clSplits = *cl->splits();

  std::unordered_set<unsigned> splits;
  for(unsigned i = 0; i < clSplits.size(); i++)
    splits.insert(clSplits[i]);

  UnitIterator parents = u->getParents();
  while(parents.hasNext()) {
    Unit *parent = parents.next();
    if(!parent->isClause())
      continue;
    Clause *cl = u->asClause();
    if(!cl->splits())
      continue;
    SplitSet &clSplits = *cl->splits();
    for(unsigned i = 0; i < clSplits.size(); i++)
      splits.insert(clSplits[i]);
  }

  for(unsigned split : splits)
    out << "(declare-const sp" << Splitter::getLiteralFromName(split).var() << " Bool)\n";
}

static void trivial(std::ostream &out, DHMap<unsigned, TermList> &conclSorts, Clause *concl) {
  UnitIterator parents = concl->getParents();
  while(parents.hasNext()) {
    Unit *parent = parents.next();
    ASS(parent->isClause())
    outputPremise(out, conclSorts, parent->asClause());
  }
  outputConclusion(out, conclSorts, concl->asClause());
}

static void resolution(std::ostream &out, DHMap<unsigned, TermList> &conclSorts, Clause *concl) {
  auto [left, right] = getParents<2>(concl);
  const auto &br = env.proofExtra.get<Inferences::BinaryResolutionExtra>(concl);

  RobSubstitution subst;
  Literal *selectedLeft = br.selectedLiteral.selectedLiteral;
  Literal *selectedRight = br.otherLiteral;
  ASS_NEQ(selectedLeft->polarity(), selectedRight->polarity())
  ALWAYS(subst.unify(TermList(selectedLeft), 0, TermList(selectedRight), 1));

  for(unsigned i = 0; i < left->length(); i++)
    if((*left)[i] != selectedLeft)
      subst.apply((*left)[i], 0);
  for(unsigned i = 0; i < right->length(); i++)
    if((*right)[i] != selectedRight)
      subst.apply((*right)[i], 1);

  outputPremise(out, conclSorts, left->asClause(), DoRobSubst<0>(subst));
  outputPremise(out, conclSorts, right->asClause(), DoRobSubst<1>(subst));
  outputConclusion(out, conclSorts, concl->asClause());
}

static void subsumptionResolution(std::ostream &out, DHMap<unsigned, TermList> &conclSorts, Clause *concl) {
  auto [left, right] = getParents<2>(concl);
  auto sr = env.proofExtra.get<Inferences::LiteralInferenceExtra>(concl);
  Literal *m = sr.selectedLiteral;

  // reconstruct match by calling into the SATSR code
  SATSubsumption::SATSubsumptionAndResolution satSR;
  ALWAYS(satSR.checkSubsumptionResolutionWithLiteral(right, left, left->getLiteralPosition(m)))
  auto subst = satSR.getBindingsForSubsumptionResolutionWithLiteral();

  outputPremise(out, conclSorts, left->asClause());
  outputPremise(out, conclSorts, right->asClause(), DoSimpleSubst(subst));
  outputConclusion(out, conclSorts, concl->asClause());
}

static void superposition(std::ostream &out, DHMap<unsigned, TermList> &conclSorts, Clause *concl) {
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
  for(unsigned i = 0; i < left->length(); i++)
    if((*left)[i] != leftSelected)
      subst.apply((*left)[i], 0);
  for(unsigned i = 0; i < right->length(); i++)
    if((*right)[i] != rightSelected)
      subst.apply((*right)[i], 1);

  outputPremise(out, conclSorts, left->asClause(), DoRobSubst<0>(subst));
  outputPremise(out, conclSorts, right->asClause(), DoRobSubst<1>(subst));
  outputConclusion(out, conclSorts, concl->asClause());
}

// check whether `demodulator` l = r rewrites left-to-right in the context of C[t] -> C[s]
// TODO copied from Dedukti, merge at some point
static bool isL2RDemodulatorFor(Literal *demodulator, Clause *rewritten, TermList target, Clause *result) {
  ASS(demodulator->isEquality())
  ASS(demodulator->isPositive())

  // TODO this is waaay overkill, but it's very hard to work out which way a demodulator was used
  // consult MH about how best to do this
  SimpleSubstitution subst;
  if(!MatchingUtils::matchTerms(demodulator->termArg(0), target, subst))
    return false;
  TermList rhsSubst = SubstHelper::apply(demodulator->termArg(1), subst);

  for(Literal *l : rewritten->iterLits())
    if(!result->contains(l) && !result->contains(EqHelper::replace(l, target, rhsSubst)))
      return false;

  return true;
}

static void demodulation(std::ostream &out, DHMap<unsigned, TermList> &conclSorts, Clause *concl) {
  auto [left, right] = getParents<2>(concl);
  auto rw = env.proofExtra.get<Inferences::RewriteInferenceExtra>(concl);

  SimpleSubstitution subst;
  Literal *rightLit = (*right)[0];
  TermList target = rw.rewritten;
  TermList from = rightLit->termArg(!isL2RDemodulatorFor(rightLit, left, target, concl));
  ASS(rightLit->isEquality())
  ASS(rightLit->isPositive())
  ASS(rightLit->termArg(0) == from || rightLit->termArg(1) == from)
  ALWAYS(MatchingUtils::matchTerms(from, target, subst))

  outputPremise(out, conclSorts, left->asClause());
  outputPremise(out, conclSorts, right->asClause(), DoSimpleSubst(subst));
  outputConclusion(out, conclSorts, concl->asClause());
}

namespace Shell {
namespace SMTCheck {

void outputTypeDecl(std::ostream &out, const std::string &name, OperatorType *type) {
  out << "(declare-fun " << Name(name);
  TermList range = type->result();

  // we don't support polymorphism yet
  ASS_EQ(type->numTypeArguments(), 0)
  // we don't support many-sorted logic yet
  ASS(type->isAllDefault())
  // we don't support many-sorted logic yet
  ASS(range.isEmpty() || range == AtomicSort::defaultSort())

  out << " (";
  for(unsigned i = 0; i < type->arity(); i++)
    out << (i == 0 ? "" : " ") << "I";
  out << ") " << (range.isEmpty() ? "Bool" : "I") << ")\n";
}

void outputStep(std::ostream &out, Unit *u) {
  InferenceRule rule = u->inference().rule();
  if(rule == InferenceRule::INPUT || rule == InferenceRule::NEGATED_CONJECTURE)
    return;

  out << "\n; step " << u->number() << "\n";
  out << "(push)\n";

  bool sorry = false;
  auto conclSorts = outputSkolemsAndGetSorts(out, u);
  outputSplits(out, u);
  switch(rule) {
  case InferenceRule::REMOVE_DUPLICATE_LITERALS:
    trivial(out, conclSorts, u->asClause());
    break;
  case InferenceRule::RESOLUTION:
    resolution(out, conclSorts, u->asClause());
    break;
  case InferenceRule::SUBSUMPTION_RESOLUTION:
    subsumptionResolution(out, conclSorts, u->asClause());
    break;
  case InferenceRule::SUPERPOSITION:
    superposition(out, conclSorts, u->asClause());
    break;
  case InferenceRule::FORWARD_DEMODULATION:
  case InferenceRule::BACKWARD_DEMODULATION:
    demodulation(out, conclSorts, u->asClause());
    break;
  default:
    sorry = true;
    out << "(echo \"sorry: " << ruleName(rule) << "\")\n";
  }
  if(!sorry) {
    out << "(set-info :status unsat)\n";
    out << "(check-sat)\n";
  }
  out << "(pop)\n";
}

}
}
