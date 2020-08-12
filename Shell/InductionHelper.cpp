#include "InductionHelper.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"

using namespace Kernel;

namespace Shell {

Term* copyTerm(Term* other) {
  ASS(!other->isSpecial());
  DArray<TermList> args(other->arity());
  Term::Iterator argIt(other);
  unsigned j = 0;
  while (argIt.hasNext()) {
    auto t = argIt.next();
    if (t.isTerm()) {
      args[j] = TermList(copyTerm(t.term()));
    } else {
      args[j] = TermList(t.var(), !t.isOrdinaryVar());
    }
    j++;
  }
  Term* res = nullptr;
  if (other->isLiteral()) {
    res = Literal::createNonShared(static_cast<Literal*>(other), args.begin());
  } else {
    res = Term::createNonShared(other, args.begin());
  }
  // TODO(mhajdu): workaround, do smth about it
  res->markShared();
  return res;
}

vstring positionToString(const TermPosition& pos) {
  vstring str;
  for (const auto& p : pos) {
    str+=Lib::Int::toString(p)+'.';
  }
  return str;
}

TermList PositionalTermReplacement::replaceIn(TermList trm)
{
  return replaceIn(trm, _p);
}

TermList PositionalTermReplacement::replaceIn(TermList trm, vvector<unsigned> rest)
{
  if (rest.empty()) {
    ASS(trm == TermList(_o));
    return _r;
  }

  ASS(trm.term()->arity() > 0);
  Term::Iterator it(trm.term());
  vvector<TermList> args(trm.term()->arity());
  unsigned i = 0;
  while (it.hasNext()) {
    auto arg = it.next();
    if (rest.front() == i+1) {
      vvector<unsigned> c(rest.begin()+1, rest.end());
      args[i] = replaceIn(arg, c);
    } else {
      args[i] = arg;
    }
    i++;
  }

  if (trm.term()->isLiteral()) {
    return TermList(Literal::createNonShared(static_cast<Literal*>(trm.term()), args.data()));
  }
  return TermList(Term::createNonShared(trm.term(), args.data()));
}

TermList VarShiftReplacement::transformSubterm(TermList trm)
{
  CALL("VarShiftReplacement::transformSubterm");

  if(trm.isVar()) {
    return TermList(trm.var()+_shift, trm.isSpecialVar());
  }
  return trm;
}

TermList VarReplacement::transformSubterm(TermList trm)
{
  CALL("VarReplacement::transformSubterm");

  if(trm.isVar() && trm.var()==_v) {
    return _r;
  }
  return trm;
}

bool IteratorByInductiveVariables::hasNext() {
  ASS(_it.hasNext() == _indVarIt.hasNext());

  while (_indVarIt.hasNext() && !_indVarIt.peekAtNext()) {
    _indVarIt.next();
    _it.next();
  }
  return _indVarIt.hasNext();
}

TermList IteratorByInductiveVariables::next() {
  ASS(hasNext());
  _indVarIt.next();
  return _it.next();
}

RDescription::RDescription(List<TermList>* recursiveCalls, TermList step, Formula* cond)
  : _recursiveCalls(recursiveCalls),
    _step(step),
    _condition(cond)
{}

Lib::vstring RDescription::toString() const
{
  List<TermList>::Iterator it(_recursiveCalls);
  Lib::vstring str = "";
  bool empty = !it.hasNext();
  if (!empty) {
    str+="(";
  }
  while (it.hasNext()) {
    str+=it.next().toString();
    if (it.hasNext()) {
      str+=" & ";
    }
  }
  if (!empty) {
    str+=") => ";
  }
  str+=_step.toString();
  return str;
}

List<TermList>::Iterator RDescription::getRecursiveCalls() const
{
  return List<TermList>::Iterator(_recursiveCalls);
}

TermList RDescription::getStep() const
{
  return _step;
}


RDescriptionInst::RDescriptionInst(List<vmap<TermList, TermList>>* recursiveCalls,
                                   vmap<TermList, TermList> step, Formula* cond)
  : _recursiveCalls(recursiveCalls),
    _step(step),
    _condition(cond)
{}

List<vmap<TermList, TermList>>*& RDescriptionInst::getRecursiveCalls()
{
  return _recursiveCalls;
}

vmap<TermList, TermList>& RDescriptionInst::getStep()
{
  return _step;
}

vstring RDescriptionInst::toString() const
{
  vstring str = "recursive calls: ";
  List<vmap<TermList, TermList>>::Iterator lIt(_recursiveCalls);
  while (lIt.hasNext()) {
    for (const auto& kv : lIt.next()) {
      str+=kv.first.toString()+" -> "+kv.second.toString()+"; ";
    }
  }
  str+="step: ";
  for (const auto& kv : _step) {
    str+=kv.first.toString()+" -> "+kv.second.toString()+"; ";
  }
  return str;
}

InductionTemplate::InductionTemplate()
  : _rDescriptions(0),
    _inductionVariables()
{}

void InductionTemplate::addRDescription(RDescription desc)
{
  List<RDescription>::push(desc, _rDescriptions);
}

vstring InductionTemplate::toString() const
{
  vstring str;
  List<RDescription>::Iterator rIt(_rDescriptions);
  str+="RDescriptions:";
  while (rIt.hasNext()) {
    str+=rIt.next().toString();
    if (rIt.hasNext()) {
      str+="; ";
    }
  }
  DArray<bool>::Iterator posIt(_inductionVariables);
  str+=" with inductive positions: (";
  while (posIt.hasNext()) {
    str+=to_string(posIt.next()).c_str();
    if (posIt.hasNext()) {
      str+=",";
    }
  }
  str+=")";
  return str;
}

const DArray<bool>& InductionTemplate::getInductionVariables() const
{
  return _inductionVariables;
}

List<RDescription>::Iterator InductionTemplate::getRDescriptions() const
{
  return List<RDescription>::Iterator(_rDescriptions);
}

void InductionTemplate::postprocess() {
  ASS(_rDescriptions != nullptr);

  _inductionVariables.init(_rDescriptions->head().getStep().term()->arity(), false);
  List<RDescription>::Iterator rIt(_rDescriptions);
  while (rIt.hasNext()) {
    auto r = rIt.next();
    auto cIt = r.getRecursiveCalls();
    auto step = r.getStep().term();
    while (cIt.hasNext()) {
      Term::Iterator argIt1(cIt.next().term());
      Term::Iterator argIt2(step);
      unsigned i = 0;
      while (argIt1.hasNext()) {
        ASS(argIt2.hasNext());
        auto t1 = argIt1.next();
        auto t2 = argIt2.next();
        if (t1 != t2 && t2.containsSubterm(t1)) {
          _inductionVariables[i] = true;
          // cout << t2.toString() << " properly contains " << t1.toString() << endl;
        } else {
          // cout << t2.toString() << " does not properly contain " << t1.toString() << endl;
        }
        i++;
      }
    }
  }
}

InductionScheme::InductionScheme()
  : _rDescriptionInstances(0),
    _activeOccurrences(),
    _maxVar(0)
{
}

void InductionScheme::init(Term* t, List<RDescription>::Iterator rdescIt, const Lib::DArray<bool>& indVars)
{
  unsigned var = 0;
  while (rdescIt.hasNext()) {
    Map<unsigned, unsigned> varMap;
    auto desc = rdescIt.next();
    vmap<TermList,TermList> stepSubst;

    IteratorByInductiveVariables termIt(t, indVars);
    IteratorByInductiveVariables stepIt(desc.getStep().term(), indVars);

    while (termIt.hasNext()) {
      auto argTerm = termIt.next();
      auto argStep = stepIt.next();
      if (stepSubst.count(argTerm) > 0) {
        continue;
      }
      replaceFreeVars(argStep, var, varMap);
      Map<unsigned, unsigned>::Iterator varIt(varMap);
      auto res = argStep.term();
      while (varIt.hasNext()) {
        unsigned var, replaced;
        varIt.next(var, replaced);
        VarReplacement cr(var,TermList(replaced,false));
        res = cr.transform(res);
      }
      stepSubst.insert(make_pair(argTerm, TermList(res)));
      // cout << stepSubst[argTerm].toString() << endl;
    }

    auto recCallSubstList = List<vmap<TermList,TermList>>::empty();
    List<TermList>::Iterator recCallsIt(desc.getRecursiveCalls());
    while (recCallsIt.hasNext()) {
      auto recCall = recCallsIt.next();
      vmap<TermList,TermList> recCallSubst;

      IteratorByInductiveVariables termIt(t, indVars);
      IteratorByInductiveVariables recCallIt(recCall.term(), indVars);

      while (termIt.hasNext()) {
        auto argTerm = termIt.next();
        auto argRecCall = recCallIt.next();
        if (recCallSubst.count(argTerm) > 0) {
          continue;
        }
        if (argRecCall.isVar()) {
          recCallSubst.insert(make_pair(argTerm, TermList(varMap.get(argRecCall.var()), false)));
        } else {
          auto res = argRecCall.term();
          Map<unsigned, unsigned>::Iterator varIt(varMap);
          while (varIt.hasNext()) {
            unsigned var, replaced;
            varIt.next(var, replaced);
            VarReplacement cr(var,TermList(replaced,false));
            res = cr.transform(res);
          }
          recCallSubst.insert(make_pair(argTerm, TermList(res)));
        }
        // cout << recCallSubst.get(argTerm).toString() << endl;
      }
      List<vmap<TermList,TermList>>::push(recCallSubst, recCallSubstList);
    }
    List<RDescriptionInst>::push(RDescriptionInst(recCallSubstList, stepSubst, nullptr), _rDescriptionInstances);
  }
  _maxVar = var;
}

void InductionScheme::addActiveOccurrences(vmap<TermList, vvector<TermPosition>> m)
{
  _activeOccurrences = m;
}

void InductionScheme::setMaxVar(unsigned maxVar)
{
  _maxVar = maxVar;
}

List<RDescriptionInst>::RefIterator InductionScheme::getRDescriptionInstances() const
{
  return List<RDescriptionInst>::RefIterator(_rDescriptionInstances);
}

vmap<TermList, vvector<TermPosition>> InductionScheme::getActiveOccurrences() const
{
  return _activeOccurrences;
}

unsigned InductionScheme::getMaxVar() const
{
  return _maxVar;
}

vstring InductionScheme::toString() const
{
  vstring str;
  str+="RDescription instances: ";
  List<RDescriptionInst>::Iterator lIt(_rDescriptionInstances);
  while (lIt.hasNext()) {
    str+=lIt.next().toString()+" ;-- ";
  }
  str+="Active occurrences: ";
  for (const auto& kv : _activeOccurrences) {
    str+="term: "+kv.first.toString()+" positions: ";
    for (const auto& pos : kv.second) {
      str+=positionToString(pos)+" ";
    }
  }
  return str;
}

void InductionScheme::replaceFreeVars(TermList t, unsigned& currVar, Map<unsigned, unsigned>& varMap) {
  if (t.isVar()) {
    if (!varMap.find(t.var())) {
      varMap.insert(t.var(), currVar++);
    }
  } else {
    Term::Iterator it(t.term());
    while (it.hasNext()) {
      replaceFreeVars(it.next(), currVar, varMap);
    }
  }
}

void InductionHelper::preprocess(Problem& prb)
{
  preprocess(prb.units());
}

void InductionHelper::preprocess(UnitList*& units)
{
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

    if (!lit->isRecFuncDef()) {
      continue;
    }
    auto lhs = lit->nthArgument(0);
    auto rhs = lit->nthArgument(1);
    auto lhterm = lhs->term();
    bool isPred = lhterm->isFormula();
    if (isPred) {
      lhterm = lhterm->getSpecialData()->getFormula()->literal();
    }

    InductionTemplate* templ = new InductionTemplate();
    TermList term(lhterm);
    processBody(*rhs, term, templ);
    templ->postprocess();

    if(env.options->showInduction()){
      env.beginOutput();
      env.out() << "[Induction] recursive function: " << lit->toString() << ", with induction template: " << templ->toString() << endl;
      env.endOutput();
    }
    env.signature->addInductionTemplate(lhterm->functor(), isPred, templ);
  }
}

void InductionHelper::filterSchemes(List<InductionScheme*>*& schemes)
{
  List<InductionScheme*>::Iterator schIt(schemes);
  while (schIt.hasNext()) {
    auto scheme = schIt.next();
    auto schIt2 = schIt;

    while (schIt2.hasNext()) {
      auto other = schIt2.next();
      if (checkSubsumption(scheme, other)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] induction scheme " << scheme->toString() << " is subsumed by " << other->toString() << endl;
          env.endOutput();
        }
        schemes = List<InductionScheme*>::remove(scheme, schemes);
      } else if (checkSubsumption(other, scheme)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] induction scheme " << other->toString() << " is subsumed by " << scheme->toString() << endl;
          env.endOutput();
        }
        if (schIt.peekAtNext() == other) {
          schIt.next();
        }
        schemes = List<InductionScheme*>::remove(other, schemes);
      } else if (checkSubsumption(scheme, other, true)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] induction scheme " << scheme->toString() << " can be merged into " << other->toString() << endl;
          env.endOutput();
        }
        mergeSchemes(scheme, other);
        schemes = List<InductionScheme*>::remove(scheme, schemes);
      } else if (checkSubsumption(other, scheme, true)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] induction scheme " << other->toString() << " can be merged into " << scheme->toString() << endl;
          env.endOutput();
        }
        if (schIt.peekAtNext() == other) {
          schIt.next();
        }
        mergeSchemes(other, scheme);
        schemes = List<InductionScheme*>::remove(other, schemes);
      }
    }
  }
}

void InductionHelper::processBody(TermList& body, TermList& header, InductionTemplate*& templ)
{
  if (body.isVar()) {
    RDescription desc(nullptr, header, nullptr);
    templ->addRDescription(desc);
    return;
  }
  auto term = body.term();
  if (!term->isSpecial() || term->isFormula()) {
    List<TermList>* recursiveCalls(0);
    processCase(header.term()->functor(), body, recursiveCalls);
    RDescription desc(recursiveCalls, header, nullptr);
    templ->addRDescription(desc);
  }
  else if (term->isMatch())
  {
    auto matchedVar = term->nthArgument(0)->var();
    unsigned index = findMatchedArgument(matchedVar, header);
    ASS(index < header.term()->arity());

    for (unsigned i = 1; i < term->arity(); i+=2) {
      auto pattern = term->nthArgument(i);
      auto matchBody = term->nthArgument(i+1);
      auto copiedHeader = copyTerm(header.term());

      auto arg = copiedHeader->nthArgument(index);
      if (arg->isVar()) {
        *arg = *pattern;
      } else {
        Substitution subst;
        subst.bind(matchedVar, pattern->term());
        SubstHelper::apply(arg->term(), subst, true);
      }
      TermList t(copiedHeader);
      processBody(*matchBody, t, templ);
    }
  }
}

void InductionHelper::processCase(const unsigned recFun, TermList& body, List<TermList>*& recursiveCalls)
{
  if (!body.isTerm()) {
    return;
  }

  auto term = body.term();
  if (term->functor() == recFun) {
    List<TermList>::push(body, recursiveCalls);
  }

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

unsigned InductionHelper::findMatchedArgument(unsigned matched, TermList& header)
{
  unsigned i = 0;
  Term::Iterator argIt(header.term());
  while (argIt.hasNext()) {
    IntList::Iterator varIt(argIt.next().freeVariables());
    bool found = false;
    while (varIt.hasNext()) {
      auto var = varIt.next();
      if (var == matched) {
        found = true;
        break;
      }
    }
    if (found) {
      break;
    }
    i++;
  }
  return i;
}

vstring substTermsToString(List<Term*>* l) {
  vstring str;
  List<Term*>::Iterator it(l);
  while (it.hasNext()) {
    str+=it.next()->toString()+"; ";
  }
  return str;
}

bool equalsUpToVariableRenaming(TermList t1, TermList t2) {
  if (t1.isVar() && t2.isVar()) {
    return true;
  }
  if (t1.isVar()) {
    return false;
  }
  if (t2.isVar()) {
    return false;
  }

  auto tt1 = t1.term();
  auto tt2 = t2.term();
  if (tt1->functor() != tt2->functor() || tt1->arity() != tt2->arity())
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

bool containsUpToVariableRenaming(TermList container, TermList contained) {
  if (contained.isVar()) {
    return true;
  }
  if (container.isVar()) {
    return false;
  }

  auto t1 = container.term();
  auto t2 = contained.term();
  if (t1->functor() == t2->functor() && t1->arity() == t2->arity())
  {
    bool equal = true;
    Term::Iterator it1(t1);
    Term::Iterator it2(t2);
    while (it1.hasNext()) {
      auto arg1 = it1.next();
      auto arg2 = it2.next();
      if (!equalsUpToVariableRenaming(arg1, arg2)) {
        equal = false;
        break;
      }
    }
    if (equal) {
      return true;
    }
  }

  Term::Iterator it1(container.term());
  while (it1.hasNext()) {
    auto arg1 = it1.next();
    if (containsUpToVariableRenaming(arg1, contained)) {
      return true;
    }
  }
  return false;
}

bool InductionHelper::checkSubsumption(InductionScheme* sch1, InductionScheme* sch2, bool onlyCheckIntersection)
{
  auto rdescIt1 = sch1->getRDescriptionInstances();
  while (rdescIt1.hasNext()) {
    auto rdesc1 = rdescIt1.next();
    auto contained = false;
    auto rdescIt2 = sch2->getRDescriptionInstances();
    while (rdescIt2.hasNext()) {
      auto rdesc2 = rdescIt2.next();
      if ((rdesc2.getRecursiveCalls() == nullptr) != (rdesc1.getRecursiveCalls() == nullptr)) {
        continue;
      }
      auto m2 = rdesc2.getStep();
      bool contained1 = true;
      for (const auto& kv : rdesc1.getStep()) {
        if (m2.count(kv.first) == 0) {
          if (!onlyCheckIntersection) {
            contained1 = false;
          }
          break;
        }
        auto s2 = m2[kv.first];
        if (!containsUpToVariableRenaming(s2, kv.second)) {
          contained1 = false;
          break;
        }
      }
      if (contained1) {
        contained = true;
        break;
      }
    }
    if (!contained) {
      return false;
    }
  }
  return true;
}

TermList shiftVarsUp(TermList t, unsigned shift) {
  if (t.isVar()) {
    return TermList(t.var()+shift, t.isSpecialVar());
  }
  VarShiftReplacement vr(shift);
  return TermList(vr.transform(t.term()));
}

void InductionHelper::mergeSchemes(InductionScheme* sch1, InductionScheme* sch2) {
  auto rdescIt1 = sch1->getRDescriptionInstances();
  auto maxVar = sch2->getMaxVar();
  while (rdescIt1.hasNext()) {
    auto rdesc1 = rdescIt1.next();
    auto rdescIt2 = sch2->getRDescriptionInstances();
    while (rdescIt2.hasNext()) {
      auto& rdesc2 = rdescIt2.next();
      bool base1 = rdesc1.getRecursiveCalls() == nullptr;
      bool base2 = rdesc2.getRecursiveCalls() == nullptr;
      if (base1 != base2) {
        continue;
      }
      auto m2 = rdesc2.getStep();
      bool contained = true;
      // if (!base1 && !base2) {
        for (const auto& kv : rdesc1.getStep()) {
          if (m2.count(kv.first) == 0) {
            continue;
          }
          auto s2 = m2[kv.first];
          if (!containsUpToVariableRenaming(s2, kv.second)) {
            contained = false;
            break;
          }
        }
      // }
      if (contained) {
        for (const auto& kv : rdesc1.getStep()) {
          if (m2.count(kv.first) == 0) {
            rdesc2.getStep().insert(
              make_pair(shiftVarsUp(kv.first, maxVar), shiftVarsUp(kv.second, maxVar)));
          }
        }
        auto mergedRecCalls = List<vmap<TermList,TermList>>::empty();
        List<vmap<TermList,TermList>>::Iterator it1(rdesc1.getRecursiveCalls());
        while (it1.hasNext()) {
          auto recCall1 = it1.next();
          List<vmap<TermList,TermList>>::Iterator it2(rdesc2.getRecursiveCalls());
          while (it2.hasNext()) {
            auto recCall2 = it2.next();
            for (const auto& kv : recCall1) {
              auto mergedRecCall = recCall2;
              mergedRecCall.insert(
                make_pair(shiftVarsUp(kv.first, maxVar), shiftVarsUp(kv.second, maxVar)));
              List<vmap<TermList,TermList>>::push(mergedRecCall, mergedRecCalls);
            }
          }
        }
        rdesc2.getRecursiveCalls() = mergedRecCalls;
      }
    }
  }
  sch2->setMaxVar(sch2->getMaxVar()+maxVar);
}

} // Shell
