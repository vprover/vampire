#include "InductionHelper.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

using namespace Kernel;

namespace Shell {

template<class T>
bool findInjectiveMapping(DHMap<T, vset<T>> sets) {
  bool change;
  do {
    change = false;
    DHMap<T, vset<T>> reverse;
    auto it = sets.items();
    while (it.hasNext()) {
      auto kv = it.next();
      if (kv.second.empty()) {
        return false;
      }
      if (kv.second.size() == 1) {
        reverse.insert(*kv.second.begin(), vset<T>());
        reverse.get(*kv.second.begin()).insert(kv.first);
      }
    }
    it = reverse.items();
    while (it.hasNext()) {
      auto kv = it.next();
      if (kv.second.size() > 1) {
        return false;
      }
      sets.remove(*kv.second.begin());
      auto it2 = sets.items();
      while (it2.hasNext()) {
        auto kv2 = it2.next();
        sets.get(kv2.first).erase(*kv.second.begin());
      }
      change = true;
    }
  } while (change);

  ASS(sets.isEmpty());
  return true;
}

Formula* applySubst(RobSubstitution& subst, int index, Formula* f) {
  if (f->connective() == Connective::LITERAL) {
    return new AtomicFormula(subst.apply(f->literal(), index));
  }

  switch (f->connective()) {
    case Connective::AND:
    case Connective::OR: {
      FormulaList* res = f->args();
      FormulaList::RefIterator it(res);
      while (it.hasNext()) {
        auto& curr = it.next();
        curr = applySubst(subst, index, curr);
      }
      return JunctionFormula::generalJunction(f->connective(), res);
    }
    case Connective::IMP:
    case Connective::XOR:
    case Connective::IFF: {
      auto left = applySubst(subst, index, f->left());
      auto right = applySubst(subst, index, f->right());
      return new BinaryFormula(f->connective(), left, right);
    }
    case Connective::NOT: {
      return new NegatedFormula(applySubst(subst, index, f->uarg()));
    }
    // case Connective::EXISTS:
    // case Connective::FORALL: {
    //   return new QuantifiedFormula(f->connective(), vars, sorts, arg);
    // }
    default:
      ASSERTION_VIOLATION;
  }
}

Formula* applyRenaming(Renaming& renaming, Formula* f) {
  if (f->connective() == Connective::LITERAL) {
    return new AtomicFormula(renaming.apply(f->literal()));
  }

  switch (f->connective()) {
    case Connective::AND:
    case Connective::OR: {
      FormulaList* res = f->args();
      FormulaList::RefIterator it(res);
      while (it.hasNext()) {
        auto& curr = it.next();
        curr = applyRenaming(renaming, curr);
      }
      return JunctionFormula::generalJunction(f->connective(), res);
    }
    case Connective::IMP:
    case Connective::XOR:
    case Connective::IFF: {
      auto left = applyRenaming(renaming, f->left());
      auto right = applyRenaming(renaming, f->right());
      return new BinaryFormula(f->connective(), left, right);
    }
    case Connective::NOT: {
      return new NegatedFormula(applyRenaming(renaming, f->uarg()));
    }
    // case Connective::EXISTS:
    // case Connective::FORALL: {
    //   return new QuantifiedFormula(f->connective(), vars, sorts, arg);
    // }
    default:
      ASSERTION_VIOLATION;
  }
}

/**
 * Checks whether sch1 is subsumed by sch2 by the following criteria:
 * - all step cases of sch1 is a subterm of some step case of sch2
 *   up to variable renaming
 * - base cases are not checked since exhaustiveness of cases and
 *   containment of step cases implies containment of base cases too
 */
bool checkSubsumption(const InductionScheme& sch1, const InductionScheme& sch2)
{
  CALL("checkSubsumption");

  DHMap<const RDescriptionInst*, vset<const RDescriptionInst*>> sch1tosch2;
  for (const auto& rdesc1 : sch1._rDescriptionInstances) {
    if (rdesc1._recursiveCalls.empty()) {
      continue;
    }
    sch1tosch2.insert(&rdesc1, vset<const RDescriptionInst*>());
    for (const auto& rdesc2 : sch2._rDescriptionInstances) {
      // only check recursive cases
      if (rdesc2._recursiveCalls.empty()) {
        continue;
      }
      for (const auto& kv : rdesc1._step) {
        // this step of sch2 does not contain ind.var from sch1 
        if (!rdesc2._step.count(kv.first)) {
          continue;
        }
        auto s2 = rdesc2._step.at(kv.first);
        RobSubstitution subst;
        // try to unify the step cases
        if (!subst.unify(s2, 0, kv.second, 1)) {
          continue;
        }
        auto t1 = subst.apply(kv.second, 1);
        Renaming r;
        r.normalizeVariables(s2);
        auto t2 = r.apply(s2);
        if (t1 != t2) {
          continue;
        }
        // check condition subsumption
        for (const auto& c1 : rdesc1._conditions) {
          bool found = false;
          for (const auto& c2 : rdesc2._conditions) {
            auto c1s = applySubst(subst, 1, c1);
            auto c2s = applyRenaming(r, c2);
            if (c1s == c2s) {
              found = true;
              break;
            }
          }
          if (!found) {
            continue;
          }
        }
        DHMap<size_t, vset<size_t>> rec1torec2;
        // if successful, find pair for each recCall in sch1
        // don't check if recCall1 or recCall2 contain kv.first
        // as they should by definition
        size_t i = 0;
        for (const auto& recCall1 : rdesc1._recursiveCalls) {
          rec1torec2.insert(i, vset<size_t>());
          size_t j = 0;
          for (const auto& recCall2 : rdesc2._recursiveCalls) {
            const auto& r1 = subst.apply(recCall1.at(kv.first), 1);
            const auto& r2 = r.apply(recCall2.at(kv.first));
            if (r1 == r2) {
              rec1torec2.get(i).insert(j);
            }
            j++;
          }
          i++;
        }
        // check if there is an injective mapping of recursive calls
        // of sch1 to matching recursive calls of sch2
        if (findInjectiveMapping(rec1torec2)) {
          sch1tosch2.get(&rdesc1).insert(&rdesc2);
        }
      }
    }
  }
  // check if there is an injective mapping of rdesc instances
  // of sch1 to matching rdesc instances of sch2
  return findInjectiveMapping(sch1tosch2);
}

bool findCommutator(const vmap<TermList, pair<TermList, TermList>>& initialGoalPairs,
  const InductionScheme& sch1, const InductionScheme& sch2, unsigned counter, bool firstRound);

bool findCommutatorHelper(const vmap<TermList, pair<TermList, TermList>>& initialGoalPairs,
  const InductionScheme& sch1, const InductionScheme& sch2, unsigned counter, bool firstRound, bool which)
{
  auto sch = which ? sch1 : sch2;
  for (const auto& rdesc : sch._rDescriptionInstances) {
    bool match = true;
    vmap<TermList, RobSubstitutionSP> pairs;
    for (const auto& kv : initialGoalPairs) {
      auto indTerm = kv.first;
      auto t1 = rdesc._step.at(indTerm);
      auto t2 = kv.second.first;
      RobSubstitutionSP subst(new RobSubstitution);
      if (!subst->unify(t1, 0, t2, 1)) {
        match = false;
        break;
      }
      pairs.insert(make_pair(indTerm, subst));
    }
    if (match) {
      for (const auto& recCall : rdesc._recursiveCalls) {
        vmap<TermList, pair<TermList,TermList>> newPairs;
        for (const auto& kv : initialGoalPairs) {
          // TODO(mhajdu): maybe check here that at least one term
          // simplifies, otherwise there can be infinite loops
          auto indTerm = kv.first;
          auto initial = pairs.at(indTerm)->apply(recCall.at(indTerm), 0);
          auto goal = kv.second.second;
          cout << "Mapped new: " << indTerm << " " << initial << " " << goal << endl;
          newPairs.insert(make_pair(indTerm, make_pair(initial, goal)));
        }
        if (findCommutator(newPairs, sch1, sch2, counter+1, firstRound)) {
          return true;
        }
      }
    }
  }
  return false;
}

bool findCommutator(const vmap<TermList, pair<TermList, TermList>>& initialGoalPairs,
  const InductionScheme& sch1, const InductionScheme& sch2, unsigned counter, bool firstRound)
{
  if (counter > 0) {
    // check if succeeded
    bool success = true;
    for (const auto& pair : initialGoalPairs) {
      auto t1 = pair.second.first;
      auto t2 = pair.second.second;
      RobSubstitution subst;
      if (!subst.unify(t1, 0, t2, 1)) {
        success = false;
        break;
      }
      Renaming r1;
      r1.normalizeVariables(t1);
      Renaming r2;
      r2.normalizeVariables(t2);
      if (subst.apply(t1, 0) != r1.apply(t1) || subst.apply(t2, 1) != r2.apply(t2)) {
        success = false;
        break;
      } 
    }
    if (success) {
      return true;
    }
  }
  if (counter > 0 && firstRound) {
    return false;
  }
  if (findCommutatorHelper(initialGoalPairs, sch1, sch2, counter, firstRound, false)) {
    return true;
  }
  return counter > 0 && findCommutatorHelper(initialGoalPairs, sch1, sch2, counter, firstRound, true);
}

bool checkQuasiCommutation(const InductionScheme& sch1, const InductionScheme& sch2) {
  cout << "checkQuasiCOmmutation" << endl;
  CALL("checkQuasiCommutation");

  // check that no condition is present
  for (const auto& rdesc : sch1._rDescriptionInstances) {
    if (!rdesc._conditions.empty()) {
      return false;
    }
  }
  for (const auto& rdesc : sch2._rDescriptionInstances) {
    if (!rdesc._conditions.empty()) {
      return false;
    }
  }

  // create terms for the relation sch2 o sch1;
  // each vector gives a tuple of initial -> goal
  // pairs for each induction term
  vvector<vmap<TermList, pair<TermList, TermList>>> terms;
  vset<TermList> usedInactiveTermsFromSch1;
  for (const auto& rdesc2 : sch2._rDescriptionInstances) {
    for (const auto& recCall2 : rdesc2._recursiveCalls) {
      for (const auto& rdesc1 : sch1._rDescriptionInstances) {
        if (rdesc1._recursiveCalls.empty()) {
          // base case, no relation
          continue;
        }
        bool match = true;
        vmap<TermList, RobSubstitutionSP> substs;
        vmap<TermList, TermList> recCallTerms;
        vset<TermList> indTerms;
        for (const auto& kv2 : recCall2) {
          auto indTerm = kv2.first;
          auto t2 = kv2.second;
          auto it = rdesc1._step.find(indTerm);
          auto inactive = sch1._inactive.count(indTerm) > 0;
          ASS(it != rdesc1._step.end() || inactive);

          if (it != rdesc1._step.end()) {
            RobSubstitutionSP subst(new RobSubstitution);
            auto t1 = it->second;
            if (!subst->unify(t1, 0, t2, 1)) {
              // one induction term does not unify, the
              // combined relation does not exist
              match = false;
              break;
            }
            substs.insert(make_pair(indTerm, subst));
            // put this outside if the below code is uncommented
            indTerms.insert(indTerm);
          } else {
            usedInactiveTermsFromSch1.insert(indTerm);
            // recCallTerms.insert(make_pair(indTerm, t2));
          }
        }
        if (match) {
          for (const auto& recCall1 : rdesc1._recursiveCalls) {
            vmap<TermList, pair<TermList,TermList>> initialGoalPairs;
            for (const auto& indTerm : indTerms) {
              TermList initial;
              TermList goal;
              auto t2 = rdesc2._step.at(indTerm);
              if (recCall1.count(indTerm)) {
                ASS(substs.count(indTerm));
                auto t1 = rdesc1._step.at(indTerm);
                initial = substs.at(indTerm)->apply(rdesc2._step.at(indTerm), 1);
                Renaming r;
                r.normalizeVariables(t1);
                goal = r.apply(recCall1.at(indTerm));
                // put this outside if the below code is uncommented
                initialGoalPairs.insert(make_pair(indTerm, make_pair(initial, goal)));
              } else {
                // ASS(recCallTerms.count(indTerm));
                // initial = t2;
                // goal = recCallTerms.at(indTerm);
              }
              cout << "Mapped: " << indTerm << " " << initial << " " << goal << endl;
            }
            terms.push_back(initialGoalPairs);
          }
        }
      }
    }
  }

  // one sch1 is needed
  for (const auto& t : terms) {
    if (!findCommutator(t, sch1, sch2, 0, !usedInactiveTermsFromSch1.empty())) {
      return false;
    }
  }
  return true;
}

bool createSingleRDescription(const RDescriptionInst& rdesc, const InductionScheme& other, RDescriptionInst& res) {
  if (rdesc._recursiveCalls.empty()) {
    return false;
  }
  vvector<Formula*> conditions;
  for (const auto& rdesc2 : other._rDescriptionInstances) {
    cout << "Creating difference of " << rdesc << " and " << rdesc2 << endl;
    if (rdesc2._recursiveCalls.empty()) {
      continue;
    }
    FormulaList* fs = FormulaList::empty();
    for (const auto& kv : rdesc._step) {
      auto t1 = kv.second;
      if (rdesc2._inactive.count(kv.first)) {
        continue;
      }
      TermList t2;
      if (rdesc2._activated.count(kv.first)) {
        t2 = kv.first;
      } else {
        ASS(rdesc2._step.count(kv.first));
        auto t2 = rdesc2._step.at(kv.first);
        RobSubstitution subst;
        if (!subst.unify(t1, 0, t2, 1)) {
          continue;
        }
      }
      cout << "Term: " << *kv.first.term() << endl;
      FormulaList::push(new AtomicFormula(
        Literal::createEquality(false, t1, t2, SortHelper::getResultSort(kv.first.term()))), fs);
    }
    for (const auto& kv : rdesc2._step) {
      auto t2 = kv.second;
      if (rdesc._inactive.count(kv.first)) {
        continue;
      }
      TermList t1;
      if (rdesc._activated.count(kv.first)) {
        t1 = kv.first;
      } else {
        ASS(rdesc._step.count(kv.first));
        auto t1 = rdesc._step.at(kv.first);
        RobSubstitution subst;
        if (!subst.unify(t1, 0, t2, 1)) {
          continue;
        }
      }
      FormulaList::push(new AtomicFormula(
        Literal::createEquality(false, t1, t2, SortHelper::getResultSort(kv.first.term()))), fs);
    }
    if (FormulaList::isEmpty(fs)) {
      return false;
    }
    conditions.push_back(JunctionFormula::generalJunction(Connective::OR, fs));
  }

  conditions.insert(conditions.end(), rdesc._conditions.begin(), rdesc._conditions.end());
  auto step = rdesc._step;
  auto recCalls = rdesc._recursiveCalls;
  res = RDescriptionInst(std::move(recCalls), std::move(step), std::move(conditions));
  return true;
}

bool createMergedRDescription(const RDescriptionInst& rdesc1, const RDescriptionInst& rdesc2,
  RDescriptionInst& res)
{
  if (rdesc1._recursiveCalls.empty() || rdesc2._recursiveCalls.empty()) {
    return false;
  }
  vmap<TermList, TermList> step;
  vmap<TermList, RobSubstitutionSP> substs;
  for (const auto& kv : rdesc1._step) {
    auto t1 = kv.second;
    if (!rdesc2._activated.count(kv.first) && !rdesc2._inactive.count(kv.first)) {
      RobSubstitutionSP subst(new RobSubstitution);
      ASS(rdesc2._step.count(kv.first));
      auto t2 = rdesc2._step.at(kv.first);
      if (!subst->unify(t1, 0, t2, 1)) {
        return false;
      }
      step.insert(make_pair(kv.first, subst->apply(t1, 0)));
      substs.insert(make_pair(kv.first, subst));
    } else {
      step.insert(make_pair(kv.first, t1));
    }
  }
  for (const auto& kv : rdesc2._step) {
    auto t2 = kv.second;
    if (!rdesc1._activated.count(kv.first) && !rdesc1._inactive.count(kv.first)) {
      RobSubstitutionSP subst(new RobSubstitution);
      ASS(rdesc1._step.count(kv.first));
      auto t1 = rdesc1._step.at(kv.first);
      if (!subst->unify(t1, 0, t2, 1)) {
        return false;
      }
      step.insert(make_pair(kv.first, subst->apply(t2, 1)));
      substs.insert(make_pair(kv.first, subst));
    } else {
      step.insert(make_pair(kv.first, t2));
    }
  }
  vvector<vmap<TermList, TermList>> recCalls;
  for (const auto& recCall : rdesc1._recursiveCalls) {
    vmap<TermList, TermList> resRecCall;
    for (const auto& kv : recCall) {
      resRecCall.insert(make_pair(kv.first,
        (substs.count(kv.first)) ?
          substs.at(kv.first)->apply(kv.second, 0) :
          kv.second));
    }
    recCalls.push_back(resRecCall);
  }
  for (const auto& recCall : rdesc2._recursiveCalls) {
    vmap<TermList, TermList> resRecCall;
    for (const auto& kv : recCall) {
      resRecCall.insert(make_pair(kv.first,
        (substs.count(kv.first)) ?
          substs.at(kv.first)->apply(kv.second, 1) :
          kv.second));
    }
    recCalls.push_back(resRecCall);
  }

  auto conditions = rdesc1._conditions;
  conditions.insert(conditions.end(), rdesc2._conditions.begin(), rdesc2._conditions.end());
  res = RDescriptionInst(std::move(recCalls), std::move(step), std::move(conditions));
  return true;
}

void addBaseCase(InductionScheme& sch) {
  
  for (const auto& rdesc : sch._rDescriptionInstances) {

  }
}

bool checkInductionTerms(const InductionScheme& sch1, const InductionScheme& sch2, vset<TermList>& additional)
{
  cout << "checkInductonTerms" << endl;
  if (includes(sch1._inductionTerms.begin(), sch1._inductionTerms.end(),
      sch2._inductionTerms.begin(), sch2._inductionTerms.end())) {
    return true;
  }
  vset<TermList> diff;
  set_difference(sch2._inductionTerms.begin(), sch2._inductionTerms.end(),
    sch1._inductionTerms.begin(), sch1._inductionTerms.end(), inserter(diff, diff.begin()));
  if (includes(sch1._inactive.begin(), sch1._inactive.end(),
    diff.begin(), diff.end())) {
    additional = diff;
    return true;
  }
  return false;
}

bool mergeSchemes(const InductionScheme& sch1, const InductionScheme& sch2, InductionScheme& res) {
  auto sch1copy = sch1;
  auto sch2copy = sch2.makeCopyWithVariablesShifted(sch1._maxVar+1);
  cout << "Merging schemes " << sch1copy << " and " << endl
       << sch2copy << endl;
  vset<TermList> additional;
  // either we can check quasi-commutation in both directions as the schemes
  // have the same induction terms or we check if one of the induction terms
  // can be a subset of the other either by itself or by activating additional
  // inactive induction terms, then we check only one way for quasi-commutation
  if ((sch1copy._inductionTerms != sch2copy._inductionTerms
    || (!checkQuasiCommutation(sch1copy, sch2copy) && !checkQuasiCommutation(sch2copy, sch1copy)))
    && (!checkInductionTerms(sch1copy, sch2copy, additional) || !checkQuasiCommutation(sch1copy, sch2copy))
    && (!checkInductionTerms(sch2copy, sch1copy, additional) || !checkQuasiCommutation(sch2copy, sch1copy))) {
      return false;
  }
  sch1copy.activateTerms(additional);
  sch2copy.activateTerms(additional);
  cout << "Merging schemes " << sch1copy << " and " << endl
       << sch2copy << endl;
  
  vvector<RDescriptionInst> resRdescs;
  for (const auto& rdesc : sch1copy._rDescriptionInstances) {
    RDescriptionInst inst;
    if (createSingleRDescription(rdesc, sch2copy, inst)) {
      cout << "Single rdesc: " << inst << endl;
      resRdescs.push_back(inst);
    }
  }
  for (const auto& rdesc : sch2copy._rDescriptionInstances) {
    RDescriptionInst inst;
    if (createSingleRDescription(rdesc, sch1copy, inst)) {
      cout << "Single rdesc: " << inst << endl;
      resRdescs.push_back(inst);
    }
  }
  for (const auto& rdesc1 : sch1copy._rDescriptionInstances) {
    for (const auto& rdesc2 : sch2copy._rDescriptionInstances) {
      RDescriptionInst inst;
      if (createMergedRDescription(rdesc1, rdesc2, inst)) {
        resRdescs.push_back(inst);
      }
    }
  }
  auto inactive = sch1copy._inactive;
  inactive.insert(sch2copy._inactive.begin(), sch2copy._inactive.end());
  res.init(std::move(resRdescs));
  res._inductionTerms.insert(additional.begin(), additional.end());
  set_difference(inactive.begin(), inactive.end(),
    additional.begin(), additional.end(),
    inserter(inactive, inactive.end()));
  res._inactive = inactive;
  for (auto& rdesc : res._rDescriptionInstances) {
    rdesc._inactive = inactive;
    // rdesc.activated = 
  }

  return true;
}

bool isSkolem(TermList t) {
  CALL("isSkolem");

  if (t.isVar()) {
    return false;
  }
  auto fn = t.term()->functor();
  auto symb = t.term()->isLiteral() ? env.signature->getPredicate(fn) : env.signature->getFunction(fn);
  return symb->skolem();
}

bool canInductOn(TermList t)
{
  CALL("canInductOn");

  if (t.isVar()) {
    return false;
  }
  return isSkolem(t);

  // induct on complex terms
  // return true;
}

bool isTermAlgebraCons(TermList t)
{
  CALL("isTermAlgebraCons");

  if (t.isVar()) {
    return false;
  }
  auto func = t.term()->functor();
  auto symb = t.term()->isLiteral() ? env.signature->getPredicate(func) : env.signature->getFunction(func);
  return symb->termAlgebraCons();
}

OperatorType* getType(TermList t)
{
  CALL("getType");

  //TODO(mhajdu): maybe handle variables?
  auto fn = t.term()->functor();
  auto symb = t.term()->isLiteral() ? env.signature->getPredicate(fn) : env.signature->getFunction(fn);
  return t.term()->isLiteral() ? symb->predType() : symb->fnType();
}

/**
 * Returns all subterms which can be inducted on for a term.
 */
vvector<TermList> getInductionTerms(TermList t)
{
  CALL("getInductionTerms");

  vvector<TermList> v;
  if (t.isVar()) {
    return v;
  }
  if (canInductOn(t)) {
    v.push_back(t);
    return v;
  }
  unsigned f = t.term()->functor();
  bool isPred = t.term()->isLiteral();

  // If function with recursive definition,
  // recurse in its active arguments
  if (env.signature->hasInductionTemplate(f, isPred)) {
    auto& templ = env.signature->getInductionTemplate(f, isPred);
    const auto& indVars = templ._inductionVariables;

    IteratorByInductiveVariables argIt(t.term(), indVars);
    while (argIt.hasNext()) {
      auto arg = argIt.next();
      auto indTerms = getInductionTerms(arg);
      v.insert(v.end(), indTerms.begin(), indTerms.end());
    }
  }
  if (isTermAlgebraCons(t)) {
    auto type = getType(t);
    //TODO(mhajdu): eventually check whether we really recurse on a specific
    // subterm of the constructor terms
    for (unsigned i = 0; i < t.term()->arity(); i++) {
      auto st = *t.term()->nthArgument(i);
      if (getType(st)->result() == type->result()) {
        auto indTerms = getInductionTerms(st);
        v.insert(v.end(), indTerms.begin(), indTerms.end());
      }
    }
  }
  return v;
}

bool matchesCase(TermList c, TermList t) {
  CALL("matchesCase");

  if (c.isVar()) {
    return true;
  }
  if (canInductOn(t)) {
    return false;
  }

  auto t1 = c.term();
  auto t2 = t.term();
  if (t1->isBoolean() != t2->isBoolean()
    || t1->functor() != t2->functor()
    || t1->arity() != t2->arity())
  {
    return false;
  }
  Term::Iterator it1(t1);
  Term::Iterator it2(t2);
  while (it1.hasNext()) {
    auto arg1 = it1.next();
    auto arg2 = it2.next();
    if (!matchesCase(arg1, arg2)) {
      return false;
    }
  }
  return true;
}

TermList TermListReplacement::transformSubterm(TermList trm)
{
  CALL("TermListReplacement::transformSubterm");

  if(trm.isVar() && _o.isVar() && trm.var() == _o.var()) {
    return _r;
  }

  if(trm.isTerm() && _o.isTerm() && trm.term()==_o.term()){
    return _r;
  }
  return trm;
}

TermList TermOccurrenceReplacement::transformSubterm(TermList trm)
{
  CALL("TermOccurrenceReplacement::transformSubterm");

  if (!canInductOn(trm)) {
    return trm;
  }

  if (!_c.find(trm)) {
    _c.insert(trm, 0);
  } else {
    _c.get(trm)++;
  }

  // The induction generalization heuristic is stored here:
  // - if we have only one active occurrence, induct on all
  // - otherwise only induct on the active occurrences
  if (_r.count(trm)) {
    const auto& o = _o.get(trm);
    // auto oc = _oc.get(trm);
    if (o->size() == 1 /*|| oc == o->size() + 1*/ || o->contains(_c.get(trm))) {
      return _r.at(trm);
    }
  }
  if (_inactive.count(trm) && isSkolem(trm)) {
    if (!_r_g.count(trm)) {
      _r_g.insert(make_pair(trm, TermList(_v++,false)));
    }
    return _r_g.at(trm);
  }
  return trm;
}

TermList VarReplacement::transformSubterm(TermList trm)
{
  CALL("VarReplacement::transformSubterm");

  if(trm.isVar()) {
    if (!_varMap.find(trm.var())) {
      _varMap.insert(trm.var(), _v++);
    }
    return TermList(_varMap.get(trm.var()), false);
  }
  return trm;
}

TermList VarShiftReplacement::transformSubterm(TermList trm) {
  if (trm.isVar()) {
    return TermList(trm.var()+_shift, trm.isSpecialVar());
  }
  return trm;
}

bool IteratorByInductiveVariables::hasNext()
{
  ASS(_it.hasNext() == (_indVarIt != _end));

  while (_indVarIt != _end && !*_indVarIt) {
    _indVarIt++;
    _it.next();
  }
  return _indVarIt != _end;
}

TermList IteratorByInductiveVariables::next()
{
  ASS(hasNext());
  _indVarIt++;
  return _it.next();
}

ostream& operator<<(ostream& out, const RDescription& rdesc)
{
  unsigned n = 0;
  if (!rdesc._conditions.empty()) {
    out << "(";
    for (const auto& c : rdesc._conditions) {
      out << *c;
      if (++n < rdesc._conditions.size()) {
        out << " & ";
      }
    }
    out << ") => ";
  }
  if (!rdesc._recursiveCalls.empty()) {
    out << "(";
    n = 0;
    for (const auto& r : rdesc._recursiveCalls) {
      out << r;
      if (++n < rdesc._recursiveCalls.size()) {
        out << " & ";
      }
    }
    out << ") => ";
  }
  out << rdesc._step;
  return out;
}

ostream& operator<<(ostream& out, const RDescriptionInst& inst)
{
  out << "conditions: ";
  for (const auto& c : inst._conditions) {
    out << *c << "; ";
  }
  out << "recursive calls: ";
  for (const auto& r : inst._recursiveCalls) {
    for (const auto& kv : r) {
      out << kv.first << " -> " << kv.second << "; ";
    }
  }
  out << "step: ";
  for (const auto& kv : inst._step) {
    out << kv.first << " -> " << kv.second << "; ";
  }
  out << "inactive terms: ";
  for (const auto& i : inst._inactive) {
    out << i << ", ";
  }
  out << "activated terms: ";
  for (const auto& a : inst._activated) {
    out << a << ", ";
  }
  return out;
}

void InductionTemplate::postprocess()
{
  CALL("InductionTemplate::postprocess");

  ASS(!_rDescriptions.empty());
  _rDescriptions.shrink_to_fit();

  // fill in bit vector of induction variables
  _inductionVariables = vvector<bool>(_rDescriptions[0]._step.term()->arity(), false);
  for (auto& rdesc : _rDescriptions) {
    auto step = rdesc._step.term();
    for (auto& r : rdesc._recursiveCalls) {
      Term::Iterator argIt1(r.term());
      Term::Iterator argIt2(step);
      unsigned i = 0;
      while (argIt1.hasNext()) {
        auto t1 = argIt1.next();
        auto t2 = argIt2.next();
        if (t1 != t2 && t2.containsSubterm(t1)) {
          _inductionVariables[i] = true;
        }
        i++;
      }
    }
  }
}

ostream& operator<<(ostream& out, const InductionTemplate& templ)
{
  out << "RDescriptions: ";
  unsigned n = 0;
  for (const auto& rdesc : templ._rDescriptions) {
    out << rdesc;
    if (++n < templ._rDescriptions.size()) {
      out << "; ";
    }
  }
  n = 0;
  out << " with inductive positions: (";
  for (const auto& b : templ._inductionVariables) {
    out << Int::toString(b);
    if (++n < templ._inductionVariables.size()) {
      out << ",";
    }
  }
  out << ")";
  return out;
}

bool InductionScheme::init(Term* t, vvector<RDescription>& rdescs, const vvector<bool>& indVars)
{
  CALL("InductionScheme::init");

  unsigned var = 0;
  for (auto& rdesc : rdescs) {
    // for each RDescription, use a new substitution and variable
    // replacement as these cases should be independent
    DHMap<unsigned, unsigned> varMap;
    vmap<TermList,TermList> stepSubst;

    IteratorByInductiveVariables termIt(t, indVars);
    IteratorByInductiveVariables stepIt(rdesc._step.term(), indVars);

    // We first map the inductive terms of t to the arguments of
    // the function header stored in the step case
    bool mismatch = false;
    bool match = termIt.hasNext();
    while (termIt.hasNext()) {
      auto argTerm = termIt.next();
      auto argStep = stepIt.next();
      auto its = getInductionTerms(argTerm);
      if (!matchesCase(argStep, argTerm)) {
        match = false;
      }
      for (auto& indTerm : its) {
        // This argument might have already been mapped
        if (stepSubst.count(indTerm) > 0) {
          if (stepSubst.at(indTerm).isTerm() && argStep.isTerm() &&
              stepSubst.at(indTerm).term()->functor() != argStep.term()->functor()) {
            // If this argument in the RDescription header contains a different
            // term algebra ctor than the already substituted one, we cannot create
            // this case
            mismatch = true;
            break;
          }
          continue;
        }
        // There may be variables in active
        // positions, these are skipped
        if (argStep.isVar()) {
          continue;
        }
        VarReplacement cr(varMap, var);
        auto res = cr.transform(argStep.term());
        stepSubst.insert(make_pair(indTerm, TermList(res)));
        _inductionTerms.insert(indTerm);
      }
    }
    if (match) {
      // The literal can be simplified, so we don't induct on it yet
      return false;
    }
    if (mismatch) {
      // We cannot properly create this case because
      // there is a mismatch between the ctors for
      // a substituted term
      continue;
    }

    // At this point all induction terms of t are mapped
    // and the case is valid, so we do the same with the
    // conditions and recursive calls too
    vvector<Formula*> condSubstList;
    for (auto& c : rdesc._conditions) {
      VarReplacement cr(varMap, var);
      auto res = cr.transform(c);
      condSubstList.push_back(res);
    }
    vvector<vmap<TermList,TermList>> recCallSubstList;
    for (auto& r : rdesc._recursiveCalls) {
      vmap<TermList,TermList> recCallSubst;

      IteratorByInductiveVariables termIt(t, indVars);
      IteratorByInductiveVariables recCallIt(r.term(), indVars);

      while (termIt.hasNext()) {
        auto argTerm = termIt.next();
        auto argRecCall = recCallIt.next();
        auto its = getInductionTerms(argTerm);
        for (auto& indTerm : its) {
          if (recCallSubst.count(indTerm) > 0) {
            continue;
          }
          if (argRecCall.isVar()) {
            // First we check if this variable is a subterm of some complex term
            // in the step (it is an induction variable position but may not be
            // changed in this case, see the check above)
            IteratorByInductiveVariables stepIt(rdesc._step.term(), indVars);
            bool found = false;
            while (stepIt.hasNext()) {
              auto argStep = stepIt.next();
              if (argStep != argRecCall && argStep.containsSubterm(argRecCall)) {
                found = true;
                break;
              }
            }
            if (found) {
              recCallSubst.insert(make_pair(
                indTerm, TermList(varMap.get(argRecCall.var()), false)));
            }
          } else {
            VarReplacement cr(varMap, var);
            auto res = cr.transform(argRecCall.term());
            recCallSubst.insert(make_pair(indTerm, TermList(res)));
          }
        }
      }
      recCallSubstList.push_back(std::move(recCallSubst));
    }
    _rDescriptionInstances.emplace_back(std::move(recCallSubstList), std::move(stepSubst), std::move(condSubstList));
  }
  // We now collect inactive/passive terms by just
  // collecting any non-induction term. For the strongest
  // hypotheses however, we need to check on a case to case
  // basis and collect anything that is not changing
  Term::Iterator it(t);
  while(it.hasNext()) {
    auto arg = it.next();
    auto ind = getInductionTerms(arg);
    ASS(ind.size() == 1);
    if (!_inductionTerms.count(ind[0])) {
      _inactive.insert(ind[0]);
    }
  }
  for (auto& rdesc : _rDescriptionInstances) {
    rdesc._inactive = _inactive;
  }
  _rDescriptionInstances.shrink_to_fit();
  _maxVar = var;
  return true;
}

void InductionScheme::init(vvector<RDescriptionInst>&& rdescs)
{
  CALL("InductionScheme::init");

  _rDescriptionInstances = rdescs;
  _inductionTerms.clear();
  unsigned var = 0;

  for (auto& rdesc : _rDescriptionInstances) {
    DHMap<unsigned, unsigned> varMap;
    VarReplacement vr(varMap, var);
    for (auto& kv : rdesc._step) {
      kv.second = kv.second.isVar()
        ? vr.transformSubterm(kv.second)
        : TermList(vr.transform(kv.second.term()));
      _inductionTerms.insert(kv.first);
    }
    for (auto& recCall : rdesc._recursiveCalls) {
      for (auto& kv : recCall) {
        kv.second = kv.second.isVar()
          ? vr.transformSubterm(kv.second)
          : TermList(vr.transform(kv.second.term()));
      }
    }
    for (auto& f : rdesc._conditions) {
      f = vr.transform(f);
    }
  }
  _maxVar = var;
}

void InductionScheme::activateTerms(const vset<TermList>& terms)
{
  vset<TermList> intersection;
  set_intersection(_inactive.begin(), _inactive.end(),
    terms.begin(), terms.end(),
    inserter(intersection, intersection.end()));

  vset<TermList> diff;
  set_difference(_inactive.begin(), _inactive.end(),
    terms.begin(), terms.end(),
    inserter(diff, diff.end()));
  
  _inactive = diff;
  for (auto& rdesc : _rDescriptionInstances) {
    rdesc._inactive = diff;
    rdesc._activated.insert(intersection.begin(), intersection.end());
  }
}

InductionScheme InductionScheme::makeCopyWithVariablesShifted(unsigned shift) const {
  InductionScheme res;
  res._inductionTerms = _inductionTerms;
  res._inactive = _inactive;
  VarShiftReplacement vsr(shift);

  for (const auto& rdesc : _rDescriptionInstances) {
    vvector<vmap<TermList, TermList>> resRecCalls;
    for (const auto& recCall : rdesc._recursiveCalls) {
      vmap<TermList, TermList> resRecCall;
      for (auto kv : recCall) {
        resRecCall.insert(make_pair(kv.first,
          kv.second.isVar()
            ? vsr.transformSubterm(kv.second)
            : TermList(vsr.transform(kv.second.term()))));
      }
      resRecCalls.push_back(resRecCall);
    }
    vmap<TermList, TermList> resStep;
    for (auto kv : rdesc._step) {
      resStep.insert(make_pair(kv.first,
        kv.second.isVar()
          ? vsr.transformSubterm(kv.second)
          : TermList(vsr.transform(kv.second.term()))));
    }
    vvector<Formula*> resCond;
    for (auto f : rdesc._conditions) {
      resCond.push_back(vsr.transform(f));
    }
    res._rDescriptionInstances.emplace_back(std::move(resRecCalls),
      std::move(resStep), std::move(resCond));
  }
  for (auto& rdesc : res._rDescriptionInstances) {
    rdesc._inactive = res._inactive;
  }
  return res;
}

ostream& operator<<(ostream& out, const InductionScheme& scheme)
{
  out << "RDescription instances: ";
  for (const auto& inst : scheme._rDescriptionInstances) {
    out << inst << " ;-- ";
  }
  out << "induction terms: ";
  for (const auto& t : scheme._inductionTerms) {
    out << t << ", ";
  }
  out << "inactive terms: ";
  for (const auto& t : scheme._inactive) {
    out << t << ", ";
  }

  return out;
}

void InductionPreprocessor::preprocess(Problem& prb)
{
  preprocess(prb.units());
}

void InductionPreprocessor::preprocess(UnitList* units)
{
  CALL("InductionPreprocessor::preprocess");

  UnitList::Iterator it(units);
  while (it.hasNext()) {
    auto unit = it.next();
    if (unit->isClause()){
      continue;
    }

    auto formula = unit->getFormula();
    while (formula->connective() == Connective::FORALL) {
      formula = formula->qarg();
    }

    if (formula->connective() != Connective::LITERAL) {
      continue;
    }

    auto lit = formula->literal();
    if (!lit->isRecursiveDefinition()) {
      continue;
    }
    auto lhs = lit->nthArgument(0);
    auto rhs = lit->nthArgument(1);
    auto lhterm = lhs->term();
    bool isPred = lhterm->isFormula();
    if (isPred) {
      lhterm = lhterm->getSpecialData()->getFormula()->literal();
    }

    InductionTemplate templ;
    TermList term(lhterm);
    processBody(*rhs, term, vvector<Formula*>(), templ);
    templ.postprocess();

    if(env.options->showInduction()){
      env.beginOutput();
      env.out() << "[Induction] recursive function: " << *lit << endl << ", with induction template: " << templ << endl;
      env.endOutput();
    }
    env.signature->addInductionTemplate(lhterm->functor(), isPred, std::move(templ));
  }
}

void InductionPreprocessor::processBody(TermList& body, TermList header, vvector<Formula*> conditions, InductionTemplate& templ)
{
  CALL("InductionPreprocessor::processBody");

  // Base case
  if (body.isVar()) {
    templ._rDescriptions.emplace_back(header, conditions);
    return;
  }
  // Recursive case
  auto term = body.term();
  if (!term->isSpecial() || term->isFormula()) {
    vvector<TermList> recursiveCalls;
    processCase(header.term()->functor(), body, recursiveCalls);
    templ._rDescriptions.emplace_back(recursiveCalls, header, conditions);
    return;
  }
  // TODO(mhajdu): Here there can be other constructs e.g. ITE, process them
  auto sd = term->getSpecialData();
  if (term->isMatch())
  {
    auto matchedVar = term->nthArgument(0)->var();

    for (unsigned i = 1; i < term->arity(); i+=2) {
      auto pattern = term->nthArgument(i);
      auto matchBody = term->nthArgument(i+1);
      // We replace the matched variable with
      // the pattern in the header and recurse
      TermListReplacement tr(TermList(matchedVar,false), *pattern);
      TermList t(tr.transform(header.term()));
      auto cond = conditions;
      for (auto& c : cond) {
        c = tr.transform(c);
      }
      processBody(*matchBody, t, cond, templ);
    }
  }
  else if (term->isITE())
  {
    auto cond1 = conditions;
    auto cond2 = conditions;
    cond1.push_back(sd->getCondition());
    cond2.push_back(new NegatedFormula(sd->getCondition()));
    processBody(*term->nthArgument(0), header, cond1, templ);
    processBody(*term->nthArgument(1), header, cond2, templ);
  }
}

void InductionPreprocessor::processCase(const unsigned recFun, TermList& body, vvector<TermList>& recursiveCalls)
{
  CALL("InductionPreprocessor::processCase");

  // If we arrived at a variable, nothing to do
  if (!body.isTerm()) {
    return;
  }

  // Check if this term is a recursive call, store it
  auto term = body.term();
  if (term->functor() == recFun) {
    recursiveCalls.push_back(body);
  }

  // Otherwise recurse into the subterms/subformulas
  if (term->isFormula()) {
    auto formula = term->getSpecialData()->getFormula();
    switch (formula->connective()) {
      case LITERAL: {
        TermList lit(formula->literal());
        processCase(recFun, lit, recursiveCalls);
        break;
      }
      case AND:
      case OR: {
        FormulaList::Iterator it(formula->args());
        while (it.hasNext()) {
          // TODO(mhajdu): maybe don't create a new Term here
          TermList ft(Term::createFormula(it.next()));
          processCase(recFun, ft, recursiveCalls);
        }
        break;
      }
      case TRUE:
      case FALSE: {
        break;
      }
#if VDEBUG
      default:
        ASSERTION_VIOLATION;
#endif
    }
  } else {
    Term::Iterator it(term);
    while (it.hasNext()) {
      auto n = it.next();
      processCase(recFun, n, recursiveCalls);
    }
  }
}

InductionSchemeGenerator::~InductionSchemeGenerator()
{
  DHMap<TermList, DHSet<unsigned>*>::Iterator aoIt(_actOccMap);
  while (aoIt.hasNext()) {
    delete aoIt.next();
  }
}

bool InductionSchemeGenerator::generate(Literal* lit) {
  CALL("InductionSchemeGenerator::generate");

  // Process all subterms of the literal to
  // be able to store occurrences of induction
  // terms. The literal itself and both sides
  // of the equality count as active positions.
  Stack<bool> actStack;
  if (lit->isEquality()) {
    actStack.push(true);
    actStack.push(true);
  } else {
    if (!process(TermList(lit), true, actStack)) {
      return false;
    }
  }
  SubtermIterator it(lit);
  while(it.hasNext()){
    TermList curr = it.next();
    bool active = actStack.pop();
    if (!process(curr, active, actStack)) {
      return false;
    }
  }
  ASS(actStack.isEmpty());
  return true;
}

void InductionSchemeGenerator::filter()
{
  CALL("InductionSchemeGenerator::filterSchemes");

  // for (unsigned i = 0; i < _schemes.size();) {
  //   bool filter = false;
  //   for (const auto& rdesc : _schemes[i]._rDescriptionInstances) {
  //     for (const auto& kv : rdesc._step) {
  //       auto term = kv.first;
  //       if (isSkolem(term)) {
  //         continue;
  //       }
  //       auto occ = _currOccMap.get(term);
  //       if (occ == 1) {
  //         filter = true;
  //         break;
  //       }
  //       SubtermIterator it(term.term());
  //       vmap<TermList,unsigned> skolemCount;
  //       while (it.hasNext()) {
  //         auto st = it.next();
  //         if (isSkolem(st)) {
  //           auto res = skolemCount.insert(make_pair(st, 0));
  //           if (!res.second) {
  //             res.first->second++;
  //           }
  //         }
  //       }
  //       bool skolemOutside = false;
  //       for (const auto kv : skolemCount) {
  //         if (kv.second*occ != _currOccMap.get(kv.first)) {
  //           // a skolem is not present only in this complex term, don't induct on it
  //           // cout << kv.first << " skolem is outside of " << term << " with " << _schemes[i] << endl;
  //           skolemOutside = true;
  //           break;
  //         }
  //       }
  //       if (skolemOutside) {
  //         filter = true;
  //         break;
  //       }
  //     }
  //     if (filter) {
  //       break;
  //     }
  //   }
  //   if (filter) {
  //     _schemes[i] = std::move(_schemes.back());
  //     _schemes.pop_back();
  //   } else {
  //     i++;
  //   }
  // }

  for (unsigned i = 0; i < _schemes.size();) {
    bool subsumed = false;
    for (unsigned j = i+1; j < _schemes.size();) {
      InductionScheme merged;
      if (checkSubsumption(_schemes[j], _schemes[i])) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] induction scheme " << _schemes[j] << " is subsumed by " << _schemes[i] << endl;
          env.endOutput();
        }
        _schemes[j] = std::move(_schemes.back());
        _schemes.pop_back();
      } else if (checkSubsumption(_schemes[i], _schemes[j])) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] induction scheme " << _schemes[i] << " is subsumed by " << _schemes[j] << endl;
          env.endOutput();
        }
        subsumed = true;
        break;
      } else if (mergeSchemes(_schemes[j], _schemes[i], merged)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] induction schemes " << _schemes[j] << " and " << _schemes[i]
                    << "are merged into:" << endl << merged << endl;
          env.endOutput();
        }
        _schemes[j] = std::move(_schemes.back());
        _schemes.pop_back();
        _schemes[i] = merged;
        break;
      } else {
        j++;
      }
    }
    if (subsumed) {
      _schemes[i] = std::move(_schemes.back());
      _schemes.pop_back();
    } else {
      i++;
    }
  }
}

bool InductionSchemeGenerator::process(TermList curr, bool active, Stack<bool>& actStack)
{
  CALL("InductionSchemeGenerator::process");

  if (!curr.isTerm()) {
    return true;
  }
  auto t = curr.term();

  // If induction term, store the occurrence
  if (canInductOn(curr)) {
    if (!_currOccMap.find(curr)) {
      _currOccMap.insert(curr, 0);
      _actOccMap.insert(curr, new DHSet<unsigned>());
    }
    if (active) {
      _actOccMap.get(curr)->insert(_currOccMap.get(curr));
    }
    _currOccMap.get(curr)++;
  }

  unsigned f = t->functor();
  bool isPred = t->isLiteral();

  // If function with recursive definition, create a scheme
  if (env.signature->hasInductionTemplate(f, isPred)) {
    auto& templ = env.signature->getInductionTemplate(f, isPred);
    const auto& indVars = templ._inductionVariables;

    for (auto it = indVars.rbegin(); it != indVars.rend(); it++) {
      actStack.push(*it && active);
    }

    if (!active) {
      return true;
    }

    IteratorByInductiveVariables argIt(t, indVars);
    bool match = true;
    while (argIt.hasNext()) {
      auto arg = argIt.next();
      auto its = getInductionTerms(arg);
      if (its.size() == 0) {
        match = false;
        break;
      }
      // TODO(mhajdu): it's not defined what happens
      // when multiple induction terms are present in
      // a subterm. If this breaks, investigate the issue
      ASS(its.size() == 1);
    }

    if (match) {
      _schemes.emplace_back();
      if (!_schemes.back().init(t, templ._rDescriptions, templ._inductionVariables)) {
        return false;
      }
    }
  // We induct on subterms of term algebra constructors
  } else if (isTermAlgebraCons(curr)) {
    for (unsigned i = 0; i < t->arity(); i++) {
      actStack.push(active);
    }
  } else {
    for (unsigned i = 0; i < t->arity(); i++) {
      actStack.push(false);
    }
  }
  return true;
}

} // Shell
