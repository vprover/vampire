#include "Lemma4.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"
#include "Lib/List.hpp"
#include "Lib/Stack.hpp"
#include "Shell/Rectify.hpp"
#include "F02Fragment/FO2Logger.hpp"

#include <algorithm>
#include <deque>
#include <unordered_map>
#include <string>
#include <unordered_set>
#include <vector>

namespace FO2Fragment {
namespace Lemmata {
namespace {

using namespace Kernel;

constexpr unsigned X = 0;
constexpr unsigned Y = 1;

struct Type2Clause {
  Kernel::Clause *clause;
  Kernel::FormulaUnit *owner;
  unsigned x;
  unsigned y;
};

TermList swapXY(TermList term)
{
  if (!term.isVar()) return term;
  if (term.var() == X) return TermList::var(Y);
  if (term.var() == Y) return TermList::var(X);
  return term;
}

bool containsBothVariables(const Literal *lit)
{
  bool hasX = false;
  bool hasY = false;
  VariableIterator it(lit);
  while (it.hasNext()) {
    TermList term = it.next();
    if (!term.isVar()) continue;
    hasX = hasX || term.var() == X;
    hasY = hasY || term.var() == Y;
  }
  return hasX && hasY;
}

Clause *normalizeClauseVariables(Clause *clause)
{
  std::unordered_map<unsigned, unsigned> varMap;
  unsigned nextVar = 0;
  for (unsigned i = 0; i < clause->length(); ++i) {
    VariableIterator it((*clause)[i]);
    while (it.hasNext()) {
      unsigned oldVar = it.next().var();
      if (varMap.find(oldVar) == varMap.end()) {
        varMap.emplace(oldVar, nextVar++);
      }
    }
  }

  if (varMap.size() > 2 || varMap.empty()) return clause;

  RobSubstitution subst;
  for (const auto &entry : varMap) {
    subst.unify(TermList::var(entry.first), 0,
                TermList::var(entry.second), 1);
  }

  Stack<Literal *> literals;
  for (unsigned i = 0; i < clause->length(); ++i) {
    literals.push(subst.apply((*clause)[i], 0));
  }
  return Clause::fromStack(literals, clause->inference());
}

bool areComplementaryUnderRename(const Literal *left, const Literal *right, bool &swap)
{
  if (left->functor() != right->functor() || left->arity() != right->arity() ||
      left->isPositive() == right->isPositive() || left->isEquality()) {
    return false;
  }

  bool exact = true;
  for (unsigned i = 0; i < left->arity(); ++i) {
    exact = exact && (*left->nthArgument(i) == *right->nthArgument(i));
  }
  if (exact) {
    swap = false;
    return true;
  }

  bool exchanged = true;
  for (unsigned i = 0; i < left->arity(); ++i) {
    exchanged = exchanged && (*left->nthArgument(i) == swapXY(*right->nthArgument(i)));
  }
  if (exchanged) {
    swap = true;
    return true;
  }
  return false;
}

Literal *swapVariables(Literal *lit)
{
  if (lit->isEquality()) {
    return Literal::createEquality(lit->isPositive(),
        swapXY(*lit->nthArgument(0)), swapXY(*lit->nthArgument(1)),
        lit->isTwoVarEquality() ? lit->twoVarEqSort() : AtomicSort::defaultSort());
  }
  std::vector<TermList> args;
  args.reserve(lit->arity());
  for (unsigned i = 0; i < lit->arity(); ++i) args.push_back(swapXY(*lit->nthArgument(i)));
  return Literal::create(lit->functor(), lit->arity(), lit->isPositive(), args.data());
}

std::string clauseKey(const Clause *clause)
{
  std::vector<std::string> literals;
  literals.reserve(clause->length());
  for (unsigned i = 0; i < clause->length(); ++i) literals.push_back((*clause)[i]->toString());
  std::sort(literals.begin(), literals.end());
  std::string key;
  for (const std::string &literal : literals) key += literal + " | ";
  return key;
}

Clause *makeClause(const std::vector<Literal *> &literals, Unit *parentA, Unit *parentB = nullptr)
{
  Stack<Literal *> stack;
  for (Literal *lit : literals) stack.push(lit);
  Inference inference = parentB
      ? Inference(NonspecificInference2(InferenceRule::RESOLUTION, parentA, parentB))
      : Inference(NonspecificInference1(InferenceRule::CLAUSIFY, parentA));
  return Clause::fromStack(stack, inference);
}

Clause *simplifyType2ClauseUnderDistinct(Clause *clause, unsigned x, unsigned y)
{
  std::vector<Literal *> remaining;
  for (unsigned i = 0; i < clause->length(); ++i) {
    Literal *lit = (*clause)[i];
    if (!lit->isEquality()) {
      remaining.push_back(lit);
      continue;
    }

    TermList left = *lit->nthArgument(0);
    TermList right = *lit->nthArgument(1);
    if (!left.isVar() || !right.isVar()) {
      remaining.push_back(lit);
      continue;
    }

    const bool reflexive = left.var() == right.var();
    const bool guardedPair = (left.var() == x && right.var() == y) ||
                             (left.var() == y && right.var() == x);
    if (!reflexive && !guardedPair) {
      remaining.push_back(lit);
      continue;
    }

    const bool equalityTrue = reflexive;
    const bool literalTrue = lit->isPositive() ? equalityTrue : !equalityTrue;
    if (literalTrue) return nullptr; // The disjunction is already true.
    // A false equality literal contributes nothing to the disjunction.
  }

  Stack<Literal *> normalized;
  for (Literal *lit : remaining) normalized.push(lit);
  return Clause::fromStack(normalized, clause->inference());
}

void resolveRestricted(const Clause *left, const Clause *right,
                       std::vector<Clause *> &resolvents)
{
  for (unsigned i = 0; i < left->length(); ++i) {
    Literal *pivotLeft = (*left)[i];
    if (pivotLeft->isEquality() || !containsBothVariables(pivotLeft)) continue;

    for (unsigned j = 0; j < right->length(); ++j) {
      Literal *pivotRight = (*right)[j];
      if (pivotRight->isEquality() || !containsBothVariables(pivotRight)) continue;

      bool swap = false;
      if (!areComplementaryUnderRename(pivotLeft, pivotRight, swap)) continue;

      std::vector<Literal *> remainder;
      for (unsigned k = 0; k < left->length(); ++k) {
        if (k != i) remainder.push_back((*left)[k]);
      }
      for (unsigned k = 0; k < right->length(); ++k) {
        if (k != j) remainder.push_back(swap ? swapVariables((*right)[k]) : (*right)[k]);
      }

      // Normalize the resolvent and discard tautologies before constructing it.
      std::vector<Literal *> normalized;
      std::unordered_set<std::string> seen;
      bool tautology = false;
      for (Literal *lit : remainder) {
        const std::string key = lit->toString();
        const std::string opposite = Literal::complementaryLiteral(lit)->toString();
        if (seen.find(opposite) != seen.end()) {
          tautology = true;
          break;
        }
        if (seen.insert(key).second) normalized.push_back(lit);
      }
      if (!tautology) {
        resolvents.push_back(makeClause(normalized, const_cast<Clause *>(left),
                                        const_cast<Clause *>(right)));
      }
    }
  }
}

Literal *formulaLiteral(Formula *formula)
{
  if (!formula) return nullptr;
  if (formula->connective() == LITERAL) return formula->literal();
  if (formula->connective() == NOT && formula->uarg() && formula->uarg()->connective() == LITERAL) {
    return Literal::create(formula->uarg()->literal(), false);
  }
  return nullptr;
}

bool appendDisjunctLiterals(Formula *formula, std::vector<Literal *> &literals)
{
  if (!formula) return false;
  if (formula->connective() == OR) {
    FormulaList::Iterator it(formula->args());
    while (it.hasNext()) {
      if (!appendDisjunctLiterals(it.next(), literals)) return false;
    }
    return true;
  }
  Literal *lit = formulaLiteral(formula);
  if (!lit) return false;
  literals.push_back(lit);
  return true;
}

bool appendCnfClauses(Formula *formula, Unit *parent, std::vector<Clause *> &clauses)
{
  if (!formula) return false;
  if (formula->connective() == AND) {
    std::vector<Clause *> extracted;
    FormulaList::Iterator it(formula->args());
    while (it.hasNext()) {
      if (!appendCnfClauses(it.next(), parent, extracted)) return false;
    }
    clauses.insert(clauses.end(), extracted.begin(), extracted.end());
    return true;
  }

  std::vector<Literal *> literals;
  if (formula->connective() == OR) {
    if (!appendDisjunctLiterals(formula, literals)) return false;
  } else {
    Literal *lit = formulaLiteral(formula);
    if (!lit) return false;
    literals.push_back(lit);
  }
  clauses.push_back(makeClause(literals, parent));
  return true;
}

bool isDistinctGuard(Literal *lit, unsigned x, unsigned y)
{
  if (!lit || !lit->isEquality() || lit->isPositive()) return false;
  TermList a = *lit->nthArgument(0);
  TermList b = *lit->nthArgument(1);
  return a.isVar() && b.isVar() &&
         ((a.var() == x && b.var() == y) || (a.var() == y && b.var() == x));
}

bool getSingleBoundVariable(Formula *formula, unsigned &var)
{
  if (!formula || !formula->vars()) return false;
  VSList::Iterator it(formula->vars());
  if (!it.hasNext()) return false;
  var = it.next().first;
  return !it.hasNext();
}

bool extractType3(FormulaUnit *unit, std::vector<Clause *> &clauses)
{
  Formula *prefix = unit->formula();
  unsigned boundCount = 0;
  while (prefix && prefix->connective() == FORALL) {
    VSList::Iterator it(prefix->vars());
    while (it.hasNext()) {
      it.next();
      ++boundCount;
    }
    prefix = prefix->qarg();
  }
  if (boundCount != 2 || !prefix || prefix->connective() == FORALL ||
      prefix->connective() == EXISTS) return false;

  std::vector<Clause *> extracted;
  if (!appendCnfClauses(prefix, unit, extracted)) return false;
  for (Clause *clause : extracted) {
    bool hasGuard = false;
    for (unsigned i = 0; i < clause->length(); ++i) {
      Literal *lit = (*clause)[i];
      if (!lit->isEquality()) continue;
      if (!lit->isPositive()) return false;
      TermList left = *lit->nthArgument(0), right = *lit->nthArgument(1);
      if (!left.isVar() || !right.isVar()) return false;
      const bool isGuard = (left.var() == X && right.var() == Y) ||
                           (left.var() == Y && right.var() == X);
      if (!isGuard) return false;
      hasGuard = true;
    }
    if (!hasGuard) return false;
  }
  clauses.insert(clauses.end(), extracted.begin(), extracted.end());
  return true;
}

bool extractType2(FormulaUnit *unit, std::vector<Clause *> &clauses,
                  unsigned &x, unsigned &y)
{
  Formula *forall = unit->formula();
  if (!forall || forall->connective() != FORALL || !getSingleBoundVariable(forall, x)) return false;
  Formula *exists = forall->qarg();
  // Lemma 3 preserves diagonal witnesses as a disjunction:
  // forall x (A(x,x) | exists y (x!=y & A(x,y))). Restricted
  // resolvents belong inside the distinct branch, not outside the choice.
  if (exists && exists->connective() == OR) {
    Formula *witness = nullptr;
    FormulaList::Iterator branches(exists->args());
    unsigned branchCount = 0;
    while (branches.hasNext()) {
      Formula *branch = branches.next();
      ++branchCount;
      if (branch->connective() == EXISTS) {
        if (witness) return false;
        witness = branch;
      }
    }
    if (branchCount != 2 || !witness) return false;
    exists = witness;
  }
  if (!exists || exists->connective() != EXISTS || !getSingleBoundVariable(exists, y)) return false;
  Formula *matrix = exists->qarg();

  std::vector<Formula *> conjuncts;
  if (matrix && matrix->connective() == AND) {
    FormulaList::Iterator it(matrix->args());
    while (it.hasNext()) conjuncts.push_back(it.next());
  } else {
    conjuncts.push_back(matrix);
  }

  std::vector<Clause *> extracted;
  bool foundGuard = false;
  for (Formula *conjunct : conjuncts) {
    Literal *lit = formulaLiteral(conjunct);
    if (lit && isDistinctGuard(lit, x, y)) {
      foundGuard = true;
      continue;
    }
    if (!appendCnfClauses(conjunct, unit, extracted)) return false;
  }
  if (!foundGuard) return false;
  for (Clause *clause : extracted) {
    for (unsigned i = 0; i < clause->length(); ++i) {
      if ((*clause)[i]->isEquality()) return false;
    }
  }
  clauses.insert(clauses.end(), extracted.begin(), extracted.end());
  return true;
}

Formula *clauseFormula(Clause *clause)
{
  FormulaList *disjuncts = FormulaList::empty();
  for (unsigned i = clause->length(); i > 0; --i) {
    FormulaList::push(new AtomicFormula((*clause)[i - 1]), disjuncts);
  }
  Formula *cnfClause = clause->length() == 0
      ? Formula::falseFormula()
      : clause->length() == 1 ? static_cast<Formula *>(new AtomicFormula((*clause)[0]))
                              : JunctionFormula::generalJunction(OR, disjuncts);
  if (clause->length() <= 1) FormulaList::destroy(disjuncts);
  return cnfClause;
}

FormulaUnit *addType2Resolvents(FormulaUnit *unit, const std::vector<Clause *> &resolvents)
{
  if (resolvents.empty()) return unit;
  Formula *forall = unit->formula();
  Formula *exists = forall->qarg();
  Formula *choice = exists->connective() == OR ? exists : nullptr;
  if (choice) {
    FormulaList::Iterator branches(choice->args());
    while (branches.hasNext()) {
      Formula *branch = branches.next();
      if (branch->connective() == EXISTS) { exists = branch; break; }
    }
  }
  Formula *matrix = exists->qarg();
  for (Clause *resolvent : resolvents) {
    FormulaList *args = FormulaList::empty();
    FormulaList::push(clauseFormula(resolvent), args);
    FormulaList::push(matrix, args);
    matrix = JunctionFormula::generalJunction(AND, args);
  }
  Formula *newExists = new QuantifiedFormula(EXISTS, exists->vars(), matrix);
  if (choice) {
    FormulaList *branches = FormulaList::empty();
    FormulaList::Iterator it(choice->args());
    while (it.hasNext()) {
      Formula *branch = it.next();
      FormulaList::push(branch == exists ? newExists : branch, branches);
    }
    newExists = JunctionFormula::generalJunction(OR, FormulaList::reverse(branches));
  }
  Formula *newForall = new QuantifiedFormula(FORALL, forall->vars(), newExists);
  return new FormulaUnit(newForall, unit->inference());
}

bool isType3RemovalCandidate(const Clause *clause)
{
  for (unsigned i = 0; i < clause->length(); ++i) {
    Literal *lit = (*clause)[i];
    if (!lit->isEquality() && containsBothVariables(lit)) return true;
  }
  return false;
}

} // namespace

void Lemma4::applyLemma4(Kernel::Problem &prb)
{
  if (FO2Logger::showsDebug()) {
    FO2Logger::logDebug("[Lemma 4] Starting restricted resolution saturation");
  }

  // Lemma 4's restricted resolution uses canonical variable IDs 0 and 1.
  // Formula rectification handles quantified formulas; clause units need a
  // separate alpha-renaming because Shell::Rectify does not rectify clauses.
  Shell::Rectify::rectify(prb.units());
  UnitList::DelIterator normalizeIt(prb.units());
  while (normalizeIt.hasNext()) {
    Unit *unit = normalizeIt.next();
    if (!unit->isClause()) continue;
    Clause *clause = static_cast<Clause *>(unit);
    Clause *normalized = normalizeClauseVariables(clause);
    if (normalized != clause) normalizeIt.replace(normalized);
  }

  std::vector<Clause *> type3;
  std::vector<Type2Clause> type2;
  std::vector<Clause *> ordinaryClauses;
  std::vector<Unit *> retainedUnits;
  std::vector<FormulaUnit *> type2Units;
  std::unordered_map<FormulaUnit *, std::vector<Clause *>> type2Additions;
  std::unordered_map<FormulaUnit *, std::unordered_set<std::string>> knownType2Resolvents;

  UnitList::DelIterator it(prb.units());
  while (it.hasNext()) {
    Unit *unit = it.next();
    if (unit->isClause()) {
      Clause *clause = static_cast<Clause *>(unit);
      bool hasTwoVar = false;
      for (unsigned i = 0; i < clause->length(); ++i) {
        if (!(*clause)[i]->isEquality() && containsBothVariables((*clause)[i])) hasTwoVar = true;
      }
      if (hasTwoVar) type3.push_back(clause);
      else ordinaryClauses.push_back(clause);
      continue;
    }

    FormulaUnit *formulaUnit = static_cast<FormulaUnit *>(unit);
    std::vector<Clause *> extracted3;
    if (extractType3(formulaUnit, extracted3)) {
      type3.insert(type3.end(), extracted3.begin(), extracted3.end());
      continue; // Replace the Type 3 formula by its CNF clauses.
    }

    std::vector<Clause *> extracted2;
    unsigned x = 0, y = 0;
    if (extractType2(formulaUnit, extracted2, x, y)) {
      for (Clause *clause : extracted2) {
        type2.push_back({clause, formulaUnit, x, y});
        knownType2Resolvents[formulaUnit].insert(clauseKey(clause));
      }
      type2Units.push_back(formulaUnit);
      continue;
    }

    retainedUnits.push_back(unit);
  }

  std::unordered_set<std::string> knownType3;
  std::deque<Clause *> passive3;
  std::vector<Clause *> active3;
  for (Clause *clause : type3) {
    if (knownType3.insert(clauseKey(clause)).second) passive3.push_back(clause);
  }

  while (!passive3.empty()) {
    Clause *given = passive3.front();
    passive3.pop_front();

    std::vector<Clause *> sameTypeResolvents;
    for (Clause *active : active3) resolveRestricted(given, active, sameTypeResolvents);
    for (Clause *resolvent : sameTypeResolvents) {
      if (knownType3.insert(clauseKey(resolvent)).second) passive3.push_back(resolvent);
    }

    active3.push_back(given);
  }

  // Once Type 3 is saturated, close the cross-resolution relation as well.
  // A newly derived Type 2 clause must be checked against every Type 3 clause,
  // including those processed before that resolvent was produced.
  std::deque<size_t> pendingType2;
  for (size_t i = 0; i < type2.size(); ++i) pendingType2.push_back(i);
  while (!pendingType2.empty()) {
    const Type2Clause parent = type2[pendingType2.front()];
    pendingType2.pop_front();
    for (Clause *type3Clause : active3) {
      std::vector<Clause *> resolvents;
      // resolveRestricted returns variables in its left parent's namespace.
      // Keep the existential owner on the left: swapping x/y on that owner
      // would turn a constraint on the universal variable into one on the
      // witness when the resolvent is inserted back into its original prefix.
      resolveRestricted(parent.clause, type3Clause, resolvents);
      for (Clause *resolvent : resolvents) {
        Clause *guardedResolvent = simplifyType2ClauseUnderDistinct(resolvent, parent.x, parent.y);
        if (!guardedResolvent) continue;
        std::string key = clauseKey(guardedResolvent);
        auto &knownForOwner = knownType2Resolvents[parent.owner];
        if (knownForOwner.insert(key).second) {
          Type2Clause derived{guardedResolvent, parent.owner, parent.x, parent.y};
          type2.push_back(derived);
          type2Additions[parent.owner].push_back(guardedResolvent);
          pendingType2.push_back(type2.size() - 1);
        }
      }
    }
  }

  UnitList *result = UnitList::empty();
  for (Unit *unit : retainedUnits) UnitList::push(unit, result);
  for (FormulaUnit *unit : type2Units) {
    UnitList::push(addType2Resolvents(unit, type2Additions[unit]), result);
  }
  for (Clause *clause : ordinaryClauses) UnitList::push(clause, result);

  // Keep precisely the Type 3 clauses without non-equality binary literals.
  for (Clause *clause : active3) {
    if (!isType3RemovalCandidate(clause)) UnitList::push(clause, result);
  }

  prb.units() = result;
  if (FO2Logger::showsDebug()) {
    FO2Logger::logDebug("[Lemma 4] Restricted resolution and Type 3 reduction complete");
  }
}

} // namespace Lemmata
} // namespace FO2Fragment
