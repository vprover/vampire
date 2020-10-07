#include "InductionHelper.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

using namespace Kernel;

namespace Shell {

bool equalsUpToVariableRenaming(TermList t1, TermList t2) {
  CALL("equalsUpToVariableRenaming");

  if (t1.isVar() && t2.isVar()) {
    return true;
  }
  if (t1.isVar() || t2.isVar()) {
    return false;
  }

  auto tt1 = t1.term();
  auto tt2 = t2.term();
  if (tt1->isBoolean() != tt2->isBoolean()
    || tt1->functor() != tt2->functor()
    || tt1->arity() != tt2->arity())
  {
    return false;
  }

  Term::Iterator it1(tt1);
  Term::Iterator it2(tt2);
  while (it1.hasNext()) {
    if (!equalsUpToVariableRenaming(it1.next(), it2.next())) {
      return false;
    }
  }
  return true;
}

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
        auto t = subst.apply(kv.second, 1);
        if (t != s2) {
          continue;
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
            const auto& r1 = recCall1.at(kv.first);
            const auto& r2 = recCall2.at(kv.first);
            if (subst.apply(r1, 1) == r2) {
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
    bool match = true;
    while (argIt.hasNext()) {
      auto arg = argIt.next();
      auto indTerms = getInductionTerms(arg);
      v.insert(v.end(), indTerms.begin(), indTerms.end());
    }
    return v;
  }
  if (!isTermAlgebraCons(t)) {
    return v;
  }
  auto type = getType(t);
  //TODO(mhajdu): eventually check whether we really recurse on a specific
  // subterm of the constructor terms
  Stack<TermList> actStack;
  actStack.push(t);
  while (actStack.isNonEmpty()) {
    auto st = actStack.pop();
    if (st.isVar()) {
      continue;
    }
    if (canInductOn(st) && getType(st)->result() == type->result()) {
      v.push_back(st);
    }
    if (isTermAlgebraCons(st)) {
      for (unsigned i = 0; i < st.term()->arity(); i++) {
        actStack.push(*st.term()->nthArgument(i));
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
  bool equal = true;
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
    auto oc = _oc.get(trm);
    if (o->size() == 1 /*|| oc == o->size() + 1*/ || o->contains(_c.get(trm))) {
      return _r.at(trm);
    }
  }
  if (_replaceSkolem && isSkolem(trm)) {
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
  bool empty = rdesc._recursiveCalls.empty();
  if (!empty) {
    out << "(";
  }
  unsigned n = 0;
  for (const auto& r : rdesc._recursiveCalls) {
    out << r;
    if (++n < rdesc._recursiveCalls.size()) {
      out << " & ";
    }
  }
  if (!empty) {
    out << ") => ";
  }
  out << rdesc._step;
  return out;
}

ostream& operator<<(ostream& out, const RDescriptionInst& inst)
{
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
    // recursive calls too
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
    _rDescriptionInstances.emplace_back(std::move(recCallSubstList), std::move(stepSubst));
  }
  _rDescriptionInstances.shrink_to_fit();
  _maxVar = var;
  return true;
}

ostream& operator<<(ostream& out, const InductionScheme& scheme)
{
  out << "RDescription instances: ";
  for (const auto& inst : scheme._rDescriptionInstances) {
    out << inst << " ;-- ";
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
    processBody(*rhs, term, templ);
    templ.postprocess();

    if(env.options->showInduction()){
      env.beginOutput();
      env.out() << "[Induction] recursive function: " << *lit << ", with induction template: " << templ << endl;
      env.endOutput();
    }
    env.signature->addInductionTemplate(lhterm->functor(), isPred, std::move(templ));
  }
}

void InductionPreprocessor::processBody(TermList& body, TermList header, InductionTemplate& templ)
{
  CALL("InductionPreprocessor::processBody");

  // Base case
  if (body.isVar()) {
    templ._rDescriptions.emplace_back(header);
    return;
  }
  // Recursive case
  auto term = body.term();
  if (!term->isSpecial() || term->isFormula()) {
    vvector<TermList> recursiveCalls;
    processCase(header.term()->functor(), body, recursiveCalls);
    templ._rDescriptions.emplace_back(recursiveCalls, header);
  }
  // TODO(mhajdu): Here there can be other constructs e.g. ITE, process them
  else if (term->isMatch())
  {
    auto matchedVar = term->nthArgument(0)->var();

    for (unsigned i = 1; i < term->arity(); i+=2) {
      auto pattern = term->nthArgument(i);
      auto matchBody = term->nthArgument(i+1);
      // We replace the matched variable with
      // the pattern in the header and recurse
      TermListReplacement tr(TermList(matchedVar,false), *pattern);
      TermList t(tr.transform(header.term()));
      processBody(*matchBody, t, templ);
    }
  }
  else if (term->isITE())
  {
    // TODO(mhajdu): Add condition here
    processBody(*term->nthArgument(0), header, templ);
    processBody(*term->nthArgument(1), header, templ);
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

  for (unsigned i = 0; i < _schemes.size();) {
    bool filter = false;
    for (const auto& rdesc : _schemes[i]._rDescriptionInstances) {
      for (const auto& kv : rdesc._step) {
        auto term = kv.first;
        if (isSkolem(term)) {
          continue;
        }
        auto occ = _currOccMap.get(term);
        if (occ == 1) {
          filter = true;
          break;
        }
        SubtermIterator it(term.term());
        vmap<TermList,unsigned> skolemCount;
        while (it.hasNext()) {
          auto st = it.next();
          if (isSkolem(st)) {
            auto res = skolemCount.insert(make_pair(st, 0));
            if (!res.second) {
              res.first->second++;
            }
          }
        }
        bool skolemOutside = false;
        for (const auto kv : skolemCount) {
          if (kv.second*occ != _currOccMap.get(kv.first)) {
            // a skolem is not present only in this complex term, don't induct on it
            // cout << kv.first << " skolem is outside of " << term << " with " << _schemes[i] << endl;
            skolemOutside = true;
            break;
          }
        }
        if (skolemOutside) {
          filter = true;
          break;
        }
      }
      if (filter) {
        break;
      }
    }
    if (filter) {
      _schemes[i] = std::move(_schemes.back());
      _schemes.pop_back();
    } else {
      i++;
    }
  }

  for (unsigned i = 0; i < _schemes.size();) {
    bool subsumed = false;
    for (unsigned j = i+1; j < _schemes.size();) {
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
