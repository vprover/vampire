#include "FO2Inferences.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/TermIterators.hpp"
#include "Lib/DHSet.hpp"

using namespace Kernel;
using namespace Lib;

namespace FO2Fragment {

/** Find an article-style split c = R1 v R2 with disjoint variable sets. */
bool FO2Inferences::partitionClause(Clause* clause, std::vector<Literal*>& r1, std::vector<Literal*>& r2)
{
  const size_t length = clause->length();
  if (length < 2) return false;

  std::vector<DHSet<unsigned>> vars(length);
  std::vector<size_t> variableLiterals;
  std::vector<size_t> groundLiterals;
  for (size_t i = 0; i < length; ++i) {
    VariableIterator it((*clause)[i]);
    while (it.hasNext()) vars[i].insert(it.next().var());
    if (vars[i].isEmpty()) groundLiterals.push_back(i);
    else variableLiterals.push_back(i);
  }

  // A ground part and a variable-bearing part are disjoint by definition.
  if (!groundLiterals.empty() && !variableLiterals.empty()) {
    for (size_t i : groundLiterals) r1.push_back((*clause)[i]);
    for (size_t i : variableLiterals) r2.push_back((*clause)[i]);
    return true;
  }

  std::vector<int> component(length, -1);
  int componentCount = 0;
  for (size_t i : variableLiterals) {
    if (component[i] != -1) continue;
    component[i] = componentCount;
    std::vector<size_t> queue{i};
    for (size_t q = 0; q < queue.size(); ++q) {
      const size_t current = queue[q];
      for (size_t j : variableLiterals) {
        if (component[j] != -1) continue;
        bool sharesVariable = false;
        DHSet<unsigned>::Iterator vit(vars[current]);
        while (vit.hasNext()) {
          if (vars[j].contains(vit.next())) { sharesVariable = true; break; }
        }
        if (sharesVariable) {
          component[j] = componentCount;
          queue.push_back(j);
        }
      }
    }
    ++componentCount;
  }

  if (componentCount < 2) return false;
  // Put the first connected component (and any ground literals) in R1;
  // collect all remaining components in R2. Their variable sets are disjoint.
  for (size_t i : groundLiterals) r1.push_back((*clause)[i]);
  for (size_t i : variableLiterals) {
    (component[i] == 0 ? r1 : r2).push_back((*clause)[i]);
  }
  return !r1.empty() && !r2.empty();
}

bool FO2Inferences::resolve(const IndexedClause& icl1, size_t litIdx1,
                            const IndexedClause& icl2, size_t litIdx2,
                            IndexedClause& outResolvent)
{
  if (litIdx1 >= icl1.length() || litIdx2 >= icl2.length()) return false;
  if (!icl1.isSelected(litIdx1) || !icl2.isSelected(litIdx2)) return false;

  Literal* lit1 = icl1[litIdx1].literal;
  Literal* lit2 = icl2[litIdx2].literal;
  if (!lit1 || !lit2) return false;
  if (lit1->functor() != lit2->functor()) return false;

  // Resolution requires complementary polarity
  if (lit1->polarity() == lit2->polarity()) return false;

  Literal* posLit1 = Literal::create(lit1, true);
  Literal* posLit2 = Literal::create(lit2, true);

  RobSubstitution subst;
  if (!subst.unify(TermList(posLit1), 0, TermList(posLit2), 1)) {
    return false;
  }

  std::vector<IndexedLiteral> resLits;

  // Add remaining literals from icl1 (bank 0)
  for (size_t i = 0; i < icl1.length(); ++i) {
    if (i == litIdx1) continue;
    Literal* subbedLit = subst.apply(icl1[i].literal, 0);
    IndexedLiteral ilit(subbedLit, icl1[i].index);
    bool dup = false;
    for (auto& existing : resLits) {
      if (existing.literal == ilit.literal && existing.index == ilit.index) {
        dup = true;
        break; 
      }
    }
    if (!dup) resLits.push_back(ilit);
  }

  // Add remaining literals from icl2 (bank 1)
  for (size_t i = 0; i < icl2.length(); ++i) {
    if (i == litIdx2) continue;
    Literal* subbedLit = subst.apply(icl2[i].literal, 1);
    IndexedLiteral ilit(subbedLit, icl2[i].index);
    bool dup = false;
    for (auto& existing : resLits) {
      if (existing.literal == ilit.literal && existing.index == ilit.index) {
        dup = true;
        break; 
      }
    }
    if (!dup) resLits.push_back(ilit);
  }

  // Tautology check: complementary literals make the resolvent tautological,
  // irrespective of their proof indices.
  for (size_t i = 0; i < resLits.size(); ++i) {
    for (size_t j = i + 1; j < resLits.size(); ++j) {
      if (Literal::complementaryLiteral(resLits[i].literal) == resLits[j].literal) {
        return false;
      }
    }
  }

  outResolvent = IndexedClause(resLits);
  return true;
}

bool FO2Inferences::factor(const IndexedClause& icl, size_t litIdx1, size_t litIdx2,
                           IndexedClause& outFactor)
{
  if (litIdx1 >= icl.length() || litIdx2 >= icl.length() || litIdx1 == litIdx2) return false;
  if (!icl.isSelected(litIdx1)) return false;

  Literal* lit1 = icl[litIdx1].literal;
  Literal* lit2 = icl[litIdx2].literal;
  if (!lit1 || !lit2) return false;
  if (lit1->functor() != lit2->functor()) return false;

  // Factoring requires same polarity
  if (lit1->polarity() != lit2->polarity()) return false;

  Literal* posLit1 = Literal::create(lit1, true);
  Literal* posLit2 = Literal::create(lit2, true);

  RobSubstitution subst;
  if (!subst.unify(TermList(posLit1), 0, TermList(posLit2), 0)) {
    return false;
  }

  std::vector<IndexedLiteral> factorLits;
  for (size_t i = 0; i < icl.length(); ++i) {
    // The factoring rule keeps the non-selected literal A2 and removes the
    // selected literal A1.
    if (i == litIdx1) continue;
    Literal* subbedLit = subst.apply(icl[i].literal, 0);
    IndexedLiteral ilit(subbedLit, icl[i].index);
    bool dup = false;
    for (auto& existing : factorLits) {
      if (existing.literal == ilit.literal && existing.index == ilit.index) {
        dup = true;
        break; 
      }
    }
    if (!dup) factorLits.push_back(ilit);
  }

  outFactor = IndexedClause(factorLits);
  return true;
}

bool FO2Inferences::simplifyWithUnit(const IndexedClause& clause,
                                   const IndexedClause& unit, IndexedClause& result)
{
  if (unit.length() != 1 || clause.length() == 0) return false;
  Literal* premise = unit[0].literal;
  for (size_t selected : clause.getSelectedLiteralIndices()) {
    const auto& target = clause[selected];
    if (target.index != unit[0].index ||
        target.literal->functor() != premise->functor() ||
        target.literal->polarity() == premise->polarity()) continue;

    // Unification alone is insufficient: p(a) cannot shorten ~p(X) | q(X)
    // to q(a), since that would discard the constraint on other values of X.
    RobSubstitution matching;
    if (!matching.match(TermList(Literal::create(premise, true)), 0,
                        TermList(Literal::create(target.literal, true)), 1)) continue;

    IndexedClause resolved, normalized;
    if (!resolve(clause, selected, unit, 0, resolved)) continue;
    normalizeVariables(resolved, normalized);
    std::string reason;
    if (!checkS2Invariant(normalized, reason) ||
        !checkIndexInvariant(normalized, reason) ||
        !subsumes(normalized, clause)) continue;
    result = normalized;
    return true;
  }
  return false;
}

namespace {
static bool matchSubsumptionLiterals(size_t litIdx1, const IndexedClause& icl1, const IndexedClause& icl2, RobSubstitution& subst, std::vector<bool>& used) {
  if (litIdx1 >= icl1.length()) {
    return true;
  }

  const IndexedLiteral& ilit1 = icl1[litIdx1];
  for (size_t j = 0; j < icl2.length(); ++j) {
    if (used[j]) continue;
    const IndexedLiteral& ilit2 = icl2[j];
    if (ilit1.index != ilit2.index) continue;
    if (ilit1.literal->polarity() != ilit2.literal->polarity()) continue;
    if (ilit1.literal->functor() != ilit2.literal->functor()) continue;

    BacktrackData bd;
    subst.bdRecord(bd);

    Literal* pos1 = Literal::create(ilit1.literal, true);
    Literal* pos2 = Literal::create(ilit2.literal, true);
    if (subst.match(TermList(pos1), 0, TermList(pos2), 1)) {
      used[j] = true;
      if (matchSubsumptionLiterals(litIdx1 + 1, icl1, icl2, subst, used)) {
        subst.bdDone();
        bd.drop();
        return true;
      }
      used[j] = false;
    }
    subst.bdDone();
    bd.backtrack();
  }
  return false;
}
} // namespace

bool FO2Inferences::subsumes(const IndexedClause& icl1, const IndexedClause& icl2)
{
  // Use occurrence-preserving (multiset) subsumption for deletion. Allowing
  // several source literals to match one target can delete required factors.
  if (icl1.length() > icl2.length()) return false;
  if (icl1.length() == 0) return true;

  RobSubstitution subst;
  std::vector<bool> used(icl2.length(), false);
  return matchSubsumptionLiterals(0, icl1, icl2, subst, used);
}

bool FO2Inferences::normalizeVariables(const IndexedClause& inIcl, IndexedClause& outIcl)
{
  DHMap<unsigned, unsigned> varMap;
  unsigned nextVar = 0;

  for (size_t i = 0; i < inIcl.length(); ++i) {
    if (!inIcl[i].literal) continue;
    VariableIterator vit(inIcl[i].literal);
    while (vit.hasNext()) {
      unsigned oldV = vit.next().var();
      if (!varMap.find(oldV)) {
        varMap.insert(oldV, nextVar++);
      }
    }
  }

  if (varMap.size() == 0) {
    outIcl = inIcl;
    return true;
  }

  RobSubstitution subst;
  DHMap<unsigned, unsigned>::Iterator vit(varMap);
  while (vit.hasNext()) {
    unsigned oldV = 0, newV = 0;
    vit.next(oldV, newV);
    subst.unify(TermList::var(oldV), 0, TermList::var(newV), 1);
  }

  std::vector<IndexedLiteral> normLits;
  for (size_t i = 0; i < inIcl.length(); ++i) {
    Literal* newLit = subst.apply(inIcl[i].literal, 0);
    IndexedLiteral ilit(newLit, inIcl[i].index);
    bool dup = false;
    for (const auto& existing : normLits) {
      if (existing == ilit) { dup = true; break; }
    }
    if (!dup) normLits.push_back(ilit);
  }

  outIcl = IndexedClause(normLits, inIcl.originClause());
  return true;
}

bool FO2Inferences::checkS2Invariant(const IndexedClause& icl, std::string& outReason)
{
  DHSet<unsigned> clauseVars;
  for (size_t i = 0; i < icl.length(); ++i) {
    if (!icl[i].literal) continue;
    VariableIterator vit(icl[i].literal);
    while (vit.hasNext()) {
      clauseVars.insert(vit.next().var());
    }
  }

  // Definition 6 (1): at most 2 variables
  if (clauseVars.size() > 2) {
    outReason = "Def.6(1): more than 2 variables";
    return false;
  }

  bool hasGroundLiteral = false;
  bool hasNonGroundLiteral = false;
  bool hasTwoVarLiteral = false;

  for (size_t i = 0; i < icl.length(); ++i) {
    Literal* lit = icl[i].literal;
    if (!lit) continue;

    DHSet<unsigned> litVars;
    VariableIterator lvit(lit);
    while (lvit.hasNext()) {
      litVars.insert(lvit.next().var());
    }

    if (litVars.size() == 0) {
      hasGroundLiteral = true;
    } else if (litVars.size() > 0) {
      hasNonGroundLiteral = true;
    }
    if (clauseVars.size() == 2 && litVars.size() == 2) {
      hasTwoVarLiteral = true;
    }

    for (unsigned a = 0; a < lit->arity(); ++a) {
      const TermList* tl = lit->nthArgument(a);
      if (!tl->isTerm()) continue;
      const Term* t = tl->term();
      // Definition 6 (1): no nested function symbols
      if (!t->isShallow()) {
        outReason = "Def.6(1): nested function symbols";
        return false;
      }
      // Definition 6 (3): non-ground functional terms contain all clause variables
      if (!t->ground()) {
        DHSet<unsigned> termVars;
        VariableIterator tvit(t);
        while (tvit.hasNext()) {
          termVars.insert(tvit.next().var());
        }
        DHSet<unsigned>::Iterator cit(clauseVars);
        while (cit.hasNext()) {
          if (!termVars.contains(cit.next())) {
            outReason = "Def.6(3): functional term does not contain all variables of the clause";
            return false;
          }
        }
      }
    }
  }

  // Definition 6 (2): ground literals only in ground clauses
  if (hasGroundLiteral && hasNonGroundLiteral) {
    outReason = "Def.6(2): ground literal in a non-ground clause";
    return false;
  }

  // Definition 6 (4): a literal containing all variables of a 2-variable clause
  if (clauseVars.size() == 2 && !hasTwoVarLiteral) {
    outReason = "Def.6(4): 2-variable clause without a literal containing both variables";
    return false;
  }

  return true;
}

namespace {
static void collectVars(const Literal* lit, DHSet<unsigned>& out)
{
  if (!lit) return;
  VariableIterator vit(lit);
  while (vit.hasNext()) {
    out.insert(vit.next().var());
  }
}
} // namespace

bool FO2Inferences::checkIndexInvariant(const IndexedClause& icl, std::string& outReason)
{
  DHSet<unsigned> clauseVars;
  for (size_t i = 0; i < icl.length(); ++i) {
    collectVars(icl[i].literal, clauseVars);
  }

  // Definition 7 constrains indices only in two-variable clauses. In
  // particular, a derived one-variable clause may retain both index 0 and
  // index 1 copies of the same literal.
  if (clauseVars.size() < 2) return true;

  for (size_t i = 0; i < icl.length(); ++i) {
    DHSet<unsigned> litVars;
    collectVars(icl[i].literal, litVars);
    const bool expectedOne = clauseVars.size() == 2 && litVars.size() == 2;
    if ((icl[i].index == 1) != expectedOne) {
      outReason = expectedOne ? "Lemma10: two-variable literal without index 1"
                              : "Lemma10: index 1 on a literal that is not two-variable";
      return false;
    }
  }
  return true;
}

bool FO2Inferences::checkSelectionCoversVars(const IndexedClause& icl, std::string& outReason)
{
  DHSet<unsigned> clauseVars;
  for (size_t i = 0; i < icl.length(); ++i) {
    collectVars(icl[i].literal, clauseVars);
  }
  if (clauseVars.size() == 0) return true; // ground clause: trivially satisfied

  for (size_t i : icl.getSelectedLiteralIndices()) {
    DHSet<unsigned> litVars;
    collectVars(icl[i].literal, litVars);
    if (litVars.size() != clauseVars.size()) {
      outReason = icl[i].literal->arity() == 0
        ? "Lemma9: selected propositional literal in a non-ground clause"
        : (litVars.size() == 0 ? "Lemma9: selected ground literal in a non-ground clause"
                               : "Lemma9: selected literal does not contain all variables");
      return false;
    }
  }
  return true;
}

} // namespace FO2Fragment
