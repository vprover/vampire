#include "InductionSchemeFilter.hpp"

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
      Renaming r;
      r.normalizeVariables(t2);
      if (subst->apply(t2, 1) != r.apply(t2)) {
        match = false;
        break;
      }
      pairs.insert(make_pair(indTerm, subst));
    }
    if (match) {
      for (const auto& recCall : rdesc._recursiveCalls) {
        vmap<TermList, pair<TermList,TermList>> newPairs;
        bool recMatch = true;
        for (const auto& kv : initialGoalPairs) {
          // TODO(mhajdu): maybe check here that at least one term
          // simplifies, otherwise there can be infinite loops
          auto indTerm = kv.first;
          auto it = recCall.find(indTerm);
          if (it == recCall.end()) {
            recMatch = false;
            break;
          }
          auto initial = pairs.at(indTerm)->apply(recCall.at(indTerm), 0);
          auto goal = kv.second.second;
          newPairs.insert(make_pair(indTerm, make_pair(initial, goal)));
        }
        if (recMatch && findCommutator(newPairs, sch1, sch2, counter+1, firstRound)) {
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

// sch2 quasi-commutes over sch1
bool checkQuasiCommutation(const InductionScheme& sch1, const InductionScheme& sch2) {
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
          ASS(it != rdesc1._step.end());

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

vvector<TermList> generateAvailableTerms(TermAlgebra* ta, unsigned& var) {
  vvector<TermList> res;
  Stack<TermList> argTerms;
  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    TermAlgebraConstructor *c = ta->constructor(i);
    argTerms.reset();

    for (unsigned j = 0; j < c->arity(); j++) {
      argTerms.push(TermList(var++, false));
    }

    res.emplace_back(Term::create(c->functor(), argTerms.size(), argTerms.begin()));
  }
  return res;
}

void excludeTermFromAvailables(vvector<TermList>& possible, TermList e, unsigned& var) {
  ASS(e.isTerm());
  auto last = possible.size();
  for (unsigned i = 0; i < last;) {
    auto p = possible[i];
    ASS(p.isTerm());
    RobSubstitution subst;
    if (subst.unify(p, 0, e, 1)) {
      // if they are unifiable, p will be either
      // replaced by more specific terms, or removed
      possible[i] = possible.back();
      possible.pop_back();
      last--;
      // if e is more special than p,
      // we go into the arguments and
      // create the remaining more special terms
      auto t1 = subst.apply(p, 0);
      Renaming r;
      r.normalizeVariables(p);
      auto t2 = r.apply(p);
      if (t1 != t2) {
        ASS(p.term()->functor()==e.term()->functor());
        vvector<TermList> newTerms;
        newTerms.push_back(p);
        Term::Iterator pIt(p.term());
        Term::Iterator eIt(e.term());
        while (pIt.hasNext()) {
          auto pArg = pIt.next();
          auto eArg = eIt.next();

          if (pArg.isVar() && eArg.isTerm()) {
            auto taSort = SortHelper::getResultSort(eArg.term());
            auto ta = env.signature->getTermAlgebraOfSort(taSort);
            auto terms = generateAvailableTerms(ta, var);
            excludeTermFromAvailables(terms, eArg, var);
            vvector<TermList> replacedTerms;
            for (auto& t : newTerms) {
              for (auto& r : terms) {
                TermListReplacement tr(pArg, r);
                replacedTerms.push_back(TermList(tr.transform(t.term())));
              }
            }
            newTerms = replacedTerms;
          }
        }
        possible.insert(possible.end(), newTerms.begin(), newTerms.end());
      }
      continue;
    }
    i++;
  }
}

bool createSingleRDescription(const RDescriptionInst& rdesc, const InductionScheme& other,
  const vset<TermList>& combinedInductionTerms, vvector<RDescriptionInst>& res)
{
  // base cases are not considered here
  if (rdesc._recursiveCalls.empty()) {
    return false;
  }
  auto recCalls = rdesc._recursiveCalls;
  auto step = rdesc._step;
  vvector<Formula*> conditions;
  vvector<vmap<TermList, vvector<TermList>>> possibleTermsList;
  unsigned var = 0;
  vmap<TermList, vvector<TermList>> possibleTermsInitial;
  for (const auto& indTerm : combinedInductionTerms) {
    auto it = rdesc._step.find(indTerm);
    if (it != rdesc._step.end() && it->second.isTerm()) {
      vvector<TermList> terms;
      terms.push_back(it->second);
      possibleTermsInitial.insert(make_pair(indTerm, terms));
    }
  }
  possibleTermsList.push_back(possibleTermsInitial);

  for (const auto& rdesc2 : other._rDescriptionInstances) {
    if (rdesc2._recursiveCalls.empty()) {
      continue;
    }
    vvector<vmap<TermList, vvector<TermList>>> nextPossibleTermsList;
    for (const auto& indTerm : combinedInductionTerms) {
      auto it1 = rdesc._step.find(indTerm);
      auto it2 = rdesc2._step.find(indTerm);
      ASS(it1 != rdesc._step.end() || it2 != rdesc2._step.end());

      if (it2 == rdesc2._step.end()) {
        continue;
      }

      auto t2 = it2->second;
      if (t2.isTerm()) {
        auto tempList = possibleTermsList;
        for (auto& possibleTerms : tempList) {
          auto pIt = possibleTerms.find(indTerm);
          if (pIt == possibleTerms.end()) {
            auto taSort = SortHelper::getResultSort(indTerm.term());
            auto ta = env.signature->getTermAlgebraOfSort(taSort);
            pIt = possibleTerms.insert(make_pair(indTerm, generateAvailableTerms(ta, var))).first;
          }
          excludeTermFromAvailables(possibleTerms.at(indTerm), t2, var);
        }
        nextPossibleTermsList.insert(nextPossibleTermsList.end(), tempList.begin(), tempList.end());
      }
    }
    possibleTermsList = nextPossibleTermsList;
  }

  res.clear();
  for (const auto& possibleTerms : possibleTermsList) {
    vvector<RDescriptionInst> temp;
    temp.push_back(rdesc);
    auto invalid = false;
    for (const auto& indTerm : combinedInductionTerms) {
      auto it = possibleTerms.find(indTerm);
      if (it != possibleTerms.end()) {
        if (it->second.empty()) {
          invalid = true;
          break;
        }
        vvector<RDescriptionInst> nextTemp;
        for (const auto& p : it->second) {
          for (auto rdesc : temp) { // intentionally copy rdesc here
            auto rIt = rdesc._step.find(indTerm);
            if (rIt != rdesc._step.end()) {
              RobSubstitution subst;
              ASS(subst.unify(rIt->second, 0, p, 1));
              rIt->second = subst.apply(rIt->second, 0);
              for (auto& cond : rdesc._conditions) {
                cond = applySubst(subst, 0, cond);
              }
              for (auto& recCall : rdesc._recursiveCalls) {
                auto recIt = recCall.find(indTerm);
                ASS(recIt != recCall.end());
                recCall.at(indTerm) = subst.apply(recIt->second, 0);
              }
            } else {
              rdesc._step.insert(make_pair(indTerm, p));
            }
            nextTemp.push_back(rdesc);
          }
        }
        temp = nextTemp;
      }
    }
    if (!invalid) {
      res.insert(res.end(), temp.begin(), temp.end());
    }
  }

  vset<TermList> diff;
  set_difference(rdesc._inactive.begin(), rdesc._inactive.end(),
    combinedInductionTerms.begin(), combinedInductionTerms.end(),
    inserter(diff, diff.end()));
  for (auto& rdesc : res) {
    rdesc._inactive = diff;
  }
  return true;
}

bool createMergedRDescription(const RDescriptionInst& rdesc1, const RDescriptionInst& rdesc2,
  const vset<TermList>& combinedInductionTerms, RDescriptionInst& res)
{
  if (rdesc1._recursiveCalls.empty() || rdesc2._recursiveCalls.empty()) {
    return false;
  }
  vmap<TermList, TermList> step;
  vmap<TermList, RobSubstitutionSP> substs;
  for (const auto& indTerm : combinedInductionTerms) {
    auto it1 = rdesc1._step.find(indTerm);
    auto it2 = rdesc2._step.find(indTerm);
    ASS(it1 != rdesc1._step.end() || it2 != rdesc2._step.end());
    if (it1 != rdesc1._step.end() && it2 != rdesc2._step.end()) {
      auto t1 = it1->second;
      auto t2 = it2->second;
      RobSubstitutionSP subst(new RobSubstitution);
      if (!subst->unify(t1, 0, t2, 1)) {
        return false;
      }
      step.insert(make_pair(indTerm, subst->apply(t1, 0)));
      substs.insert(make_pair(indTerm, subst));
    } else if (it1 != rdesc1._step.end()) {
      step.insert(make_pair(indTerm, it1->second));
    } else if (it2 != rdesc2._step.end()) {
      step.insert(make_pair(indTerm, it2->second));
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
    bool contains = false;
    for (const auto& other : recCalls) {
      if (other == resRecCall) {
        contains = true;
        break;
      }
    }
    if (!contains) {
      recCalls.push_back(resRecCall);
    }
  }

  auto conditions = rdesc1._conditions;
  conditions.insert(conditions.end(), rdesc2._conditions.begin(), rdesc2._conditions.end());
  res = RDescriptionInst(std::move(recCalls), std::move(step), std::move(conditions));

  auto inactive = rdesc1._inactive;
  inactive.insert(rdesc2._inactive.begin(), rdesc2._inactive.end());
  vset<TermList> diff;
  set_difference(inactive.begin(), inactive.end(),
    combinedInductionTerms.begin(), combinedInductionTerms.end(),
    inserter(diff, diff.end()));
  res._inactive = diff;
  return true;
}

void addBaseCase(InductionScheme& sch) {
  unsigned var = 0;
  vvector<vmap<TermList, vvector<TermList>>> possibleTermsList;
  possibleTermsList.emplace_back();
  for (const auto& rdesc : sch._rDescriptionInstances) {
    vvector<vmap<TermList, vvector<TermList>>> nextPossibleTermsList;
    for (const auto& kv : rdesc._step) {
      if (kv.second.isTerm()) {
        auto tempList = possibleTermsList;
        for (auto& possibleTerms : tempList) {
          auto pIt = possibleTerms.find(kv.first);
          if (pIt == possibleTerms.end()) {
            auto taSort = SortHelper::getResultSort(kv.first.term());
            auto ta = env.signature->getTermAlgebraOfSort(taSort);
            pIt = possibleTerms.insert(make_pair(kv.first, generateAvailableTerms(ta, var))).first;
          }
          excludeTermFromAvailables(pIt->second, kv.second, var);
        }
        remove_if(tempList.begin(), tempList.end(), [](vmap<TermList, vvector<TermList>>& e) {return e.empty();});
        nextPossibleTermsList.insert(nextPossibleTermsList.end(), tempList.begin(), tempList.end());
      }
    }
    possibleTermsList = nextPossibleTermsList;
  }

  vset<vmap<TermList, TermList>> steps;
  for (const auto& possibleTerms : possibleTermsList) {
    vvector<vmap<TermList, TermList>> temp;
    temp.emplace_back();
    auto invalid = false;
    for (const auto& kv : possibleTerms) {
      if (kv.second.empty()) {
        invalid = true;
        break;
      }
      vvector<vmap<TermList, TermList>> newTemp;
      for (const auto& p : kv.second) {
        for (auto step : temp) { // intentionally copy rdesc here
          auto rIt = step.find(kv.first);
          ASS(rIt == step.end());
          step.insert(make_pair(kv.first, p));
          newTemp.push_back(step);
        }
      }
      temp = newTemp;
    }
    if (!invalid) {
      steps.insert(temp.begin(), temp.end());
    }
  }

  for (auto step : steps) {
    vvector<vmap<TermList,TermList>> emptyRecCalls;
    vvector<Formula*> emptyConds;
    sch._rDescriptionInstances.emplace_back(std::move(emptyRecCalls), std::move(step), std::move(emptyConds));
  }
}

bool checkInductionTerms(const InductionScheme& sch1, const InductionScheme& sch2, vset<TermList>& combined)
{
  if (includes(sch1._inductionTerms.begin(), sch1._inductionTerms.end(),
      sch2._inductionTerms.begin(), sch2._inductionTerms.end())) {
    return true;
  }
  if (env.options->inductionForceMerge()) {
    vset<TermList> diff;
    set_difference(sch2._inductionTerms.begin(), sch2._inductionTerms.end(),
      sch1._inductionTerms.begin(), sch1._inductionTerms.end(), inserter(diff, diff.begin()));
    if (includes(sch1._inactive.begin(), sch1._inactive.end(),
      diff.begin(), diff.end())) {
      combined = sch1._inductionTerms;
      combined.insert(diff.begin(), diff.end());
      return true;
    }
  }
  return false;
}

bool InductionSchemeFilter::mergeSchemes(const InductionScheme& sch1, const InductionScheme& sch2, InductionScheme& res) {
  vset<TermList> combinedInductionTerms;
  // either we can check quasi-commutation in both directions as the schemes
  // have the same induction terms or we check if one of the induction terms
  // can be a subset of the other either by itself or by activating additional
  // inactive induction terms, then we check only one way for quasi-commutation
  InductionScheme sch1copy;
  InductionScheme sch2copy;

  // cout << "Merging schemes:" << endl
  //      << "1: " << sch1 << endl
  //      << "2: " << sch2 << endl;
  if (sch1._inductionTerms != sch2._inductionTerms
    || (!checkQuasiCommutation(sch1, sch2) && !checkQuasiCommutation(sch2, sch1)))
  {
    if (checkInductionTerms(sch2, sch1, combinedInductionTerms) && checkQuasiCommutation(sch2, sch1)) {
      sch1copy = sch1;
      sch2copy = sch2.makeCopyWithVariablesShifted(sch1copy._maxVar+1);
      sch2copy.addInductionTerms(combinedInductionTerms);
      // cout << "1 quasi-commutes over 2" << endl;
    } else if (checkInductionTerms(sch1, sch2, combinedInductionTerms) && checkQuasiCommutation(sch1, sch2)) {
      sch1copy = sch1;
      sch1copy.addInductionTerms(combinedInductionTerms);
      sch2copy = sch2.makeCopyWithVariablesShifted(sch1copy._maxVar+1);
      // cout << "2 quasi-commutes over 1" << endl;
    } else {
      return false;
    }
  } else {
    sch1copy = sch1;
    sch2copy = sch2.makeCopyWithVariablesShifted(sch1copy._maxVar+1);
    // cout << "1 and 2 contain the same set of variables" << endl;
  }
  // 
  if (combinedInductionTerms.empty()) {
    combinedInductionTerms.insert(sch1copy._inductionTerms.begin(), sch1copy._inductionTerms.end());
    combinedInductionTerms.insert(sch2copy._inductionTerms.begin(), sch2copy._inductionTerms.end());
  }
  // cout << "combinedInductionTerms: ";
  // for (const auto& indTerm : combinedInductionTerms) {
  //   cout << indTerm << " ";
  // }
  // cout << endl;

  vvector<RDescriptionInst> resRdescs;
  for (const auto& rdesc : sch1copy._rDescriptionInstances) {
    vvector<RDescriptionInst> inst;
    if (createSingleRDescription(rdesc, sch2copy, combinedInductionTerms, inst)) {
      resRdescs.insert(resRdescs.end(), inst.begin(), inst.end());
    }
  }
  for (const auto& rdesc : sch2copy._rDescriptionInstances) {
    vvector<RDescriptionInst> inst;
    if (createSingleRDescription(rdesc, sch1copy, combinedInductionTerms, inst)) {
      resRdescs.insert(resRdescs.end(), inst.begin(), inst.end());
    }
  }
  for (const auto& rdesc1 : sch1copy._rDescriptionInstances) {
    for (const auto& rdesc2 : sch2copy._rDescriptionInstances) {
      RDescriptionInst inst;
      if (createMergedRDescription(rdesc1, rdesc2, combinedInductionTerms, inst)) {
        resRdescs.push_back(inst);
      }
    }
  }
  res.init(std::move(resRdescs));
  addBaseCase(res);

  return true;
}

void mergeLitClausePairsInto(DHMap<Literal*, Clause*>* from, DHMap<Literal*, Clause*>* to)
{
  DHMap<Literal*, Clause*>::Iterator it(*from);
  while (it.hasNext()) {
    Literal* lit;
    Clause* cl;
    it.next(lit, cl);
    ASS(!to->find(lit) || to->get(lit) == cl); // if this happens, a more complicated structure is needed
    to->insert(lit, cl);
  }
}

void InductionSchemeFilter::filter(vvector<pair<InductionScheme, DHMap<Literal*, Clause*>*>>& primary,
    vvector<pair<InductionScheme, DHMap<Literal*, Clause*>*>>& secondary)
{
  CALL("InductionSchemeGenerator::filter");

  filter(primary);
  filter(secondary);

  // merge secondary schemes into primary ones if possible, remove the rest
  for (unsigned i = 0; i < secondary.size(); i++) {
    for (unsigned j = 0; j < primary.size(); j++) {
      auto& p = primary[j];
      auto& s = secondary[i];
      InductionScheme merged;
      if (checkSubsumption(s.first, p.first)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] secondary induction scheme " << s.first
                    << " is subsumed by primary " << p.first << endl;
          env.endOutput();
        }
        mergeLitClausePairsInto(s.second, p.second);
      } else if (checkSubsumption(p.first, s.first)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] primary induction scheme " << p.first
                    << " is subsumed by secondary " << s.first << endl;
          env.endOutput();
        }
        mergeLitClausePairsInto(s.second, p.second);
        p.first = std::move(s.first);
      } else if (mergeSchemes(p.first, s.first, merged)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] primary induction scheme " << p.first
                    << " and secondary induction scheme " << s.first
                    << " are merged into:" << endl << merged << endl;
          env.endOutput();
        }
        p.first = std::move(merged);
        mergeLitClausePairsInto(s.second, p.second);
        break;
      }
    }
  }
  for (auto& kv : secondary) {
    delete kv.second;
  }
  secondary.clear();
}

void InductionSchemeFilter::filter(vvector<pair<InductionScheme, DHMap<Literal*, Clause*>*>>& schemes)
{
  CALL("InductionSchemeGenerator::filterSchemes");

  for (unsigned i = 0; i < schemes.size();) {
    bool subsumed = false;
    for (unsigned j = i+1; j < schemes.size();) {
      InductionScheme merged;
      if (checkSubsumption(schemes[j].first, schemes[i].first)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] induction scheme " << schemes[j].first
                    << " is subsumed by " << schemes[i].first << endl;
          env.endOutput();
        }
        mergeLitClausePairsInto(schemes[j].second, schemes[i].second);
        schemes[j] = std::move(schemes.back());
        schemes.pop_back();
      } else if (checkSubsumption(schemes[i].first, schemes[j].first)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] induction scheme " << schemes[i].first
                    << " is subsumed by " << schemes[j].first << endl;
          env.endOutput();
        }
        mergeLitClausePairsInto(schemes[i].second, schemes[j].second);
        subsumed = true;
        break;
      } else if (mergeSchemes(schemes[j].first, schemes[i].first, merged)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] induction schemes " << schemes[j].first
                    << " and " << schemes[i].first
                    << "are merged into:" << endl << merged << endl;
          env.endOutput();
        }
        schemes[j] = std::move(schemes.back());
        schemes.pop_back();
        schemes[i].first = merged;
        mergeLitClausePairsInto(schemes[j].second, schemes[i].second);
        break;
      } else {
        j++;
      }
    }
    if (subsumed) {
      schemes[i] = std::move(schemes.back());
      schemes.pop_back();
    } else {
      i++;
    }
  }
}

/**
 * Checks whether sch1 is subsumed by sch2 by the following criteria:
 * - all step cases of sch1 is a subterm of some step case of sch2
 *   up to variable renaming
 * - base cases are not checked since exhaustiveness of cases and
 *   containment of step cases implies containment of base cases too
 */
bool InductionSchemeFilter::checkSubsumption(const InductionScheme& sch1, const InductionScheme& sch2)
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
        Renaming r1, r2;
        r1.normalizeVariables(kv.second);
        r2.normalizeVariables(s2);
        auto t2 = subst.apply(s2, 0);
        if (t1 != r1.apply(kv.second) || t2 != r2.apply(s2)) {
          continue;
        }
        // check condition subsumption
        for (const auto& c1 : rdesc1._conditions) {
          bool found = false;
          for (const auto& c2 : rdesc2._conditions) {
            auto c1s = applySubst(subst, 1, c1);
            auto c2s = applySubst(subst, 0, c2);
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
            if (!recCall1.count(kv.first) || !recCall2.count(kv.first)) {
              continue;
            }
            const auto& r1 = subst.apply(recCall1.at(kv.first), 1);
            const auto& r2 = subst.apply(recCall2.at(kv.first), 0);
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

} // Shell
