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

InductionScheme::InductionScheme(Term* t, vvector<unsigned> pos, InductionTemplate* templ)
  : _termPosPairs(0),
    _templ(templ),
    _activeOccurrences()
{
  addTermPosPair(t, pos);
}

void InductionScheme::addTermPosPair(Term* t, vvector<unsigned> pos)
{
  List<pair<Term*,vvector<unsigned>>>::push(make_pair(t, pos), _termPosPairs);
}

void InductionScheme::addActiveOccurrences(vmap<TermList, vvector<TermPosition>> m)
{
  _activeOccurrences = m;
}

List<pair<Term*,vvector<unsigned>>>::Iterator InductionScheme::getTermPosPairs() const
{
  return List<pair<Term*,vvector<unsigned>>>::Iterator(_termPosPairs);
}

InductionTemplate* InductionScheme::getTemplate() const
{
  return _templ;
}

vmap<TermList, vvector<TermPosition>> InductionScheme::getActiveOccurrences() const
{
  return _activeOccurrences;
}

vstring InductionScheme::toString() const
{
  vstring str;
  str+="Terms: ";
  auto it = getTermPosPairs();
  while (it.hasNext()) {
    auto pair = it.next();
    str+=pair.first->toString()+" in pos ";
    List<unsigned>::Iterator lit();
    for (const auto& p : pair.second) {
      str+=Lib::Int::toString(p)+".";
    }
    str+="; ";
  }
  str+="Scheme: "+_templ->toString()+"; ";
  str+="Active occurrences: ";
  for (const auto& kv : _activeOccurrences) {
    str+="term: "+kv.first.toString()+" positions: ";
    for (const auto& pos : kv.second) {
      str+=positionToString(pos)+" ";
    }
  }
  return str;
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

    // cout << "Recursive function: " << lit->toString() << " functor " << lhterm->functor()
    //      << ", predicate " << isPred << ", with induction template: " << templ->toString() << endl;
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
        // cout << scheme->toString() << " is subsumed by " << other->toString() << endl;
        auto termPosIt = scheme->getTermPosPairs();
        while (termPosIt.hasNext()) {
          auto p = termPosIt.next();
          other->addTermPosPair(p.first, p.second);
        }
        schemes = List<InductionScheme*>::remove(scheme, schemes);
        break;
      }
      if (checkSubsumption(other, scheme)) {
        // cout << other->toString() << " is subsumed by " << scheme->toString() << endl;
        auto termPosIt = other->getTermPosPairs();
        while (termPosIt.hasNext()) {
          auto p = termPosIt.next();
          scheme->addTermPosPair(p.first, p.second);
        }
        if (schIt.peekAtNext() == other) {
          schIt.next();
        }
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

bool InductionHelper::checkSubsumption(InductionScheme* sch1, InductionScheme* sch2)
{
  // at this stage only one term should be in each scheme
  auto t1 = sch1->getTermPosPairs().next().first;
  auto t2 = sch2->getTermPosPairs().next().first;
  auto templ1 = sch1->getTemplate();
  auto templ2 = sch2->getTemplate();

  List<RDescription>::Iterator rdescIt1(templ1->getRDescriptions());
  while (rdescIt1.hasNext()) {
    auto rdesc1 = rdescIt1.next();
    auto recCallIt1 = rdesc1.getRecursiveCalls();
    while (recCallIt1.hasNext()) {
      auto recCall1 = recCallIt1.next();
      auto substTerms1 = getSubstitutedTerms(t1, rdesc1.getStep().term(), recCall1.term(), templ1->getInductionVariables());

      List<RDescription>::Iterator rdescIt2(templ2->getRDescriptions());
      while (rdescIt2.hasNext()) {
        auto rdesc2 = rdescIt2.next();

        auto recCallIt2 = rdesc2.getRecursiveCalls();
        while (recCallIt2.hasNext()) {
          auto recCall2 = recCallIt2.next();
          auto substTerms2 = getSubstitutedTerms(t2, rdesc2.getStep().term(), recCall2.term(), templ2->getInductionVariables());

          if (!checkAllContained(substTerms1, substTerms2)) {
            return false;
          }
        }
      }
    }
  }
  return true;
}

List<Term*>* InductionHelper::getSubstitutedTerms(Term* term, Term* step, Term* recursiveCall, const DArray<bool>& indVars)
{
  List<Term*>* res(0);
  IteratorByInductiveVariables termIt(term, indVars);
  IteratorByInductiveVariables stepIt(step, indVars);
  IteratorByInductiveVariables recIt(recursiveCall, indVars);

  while (termIt.hasNext()) {
    ASS(stepIt.hasNext() && recIt.hasNext());

    auto termArg = termIt.next();
    auto stepArg = stepIt.next();
    auto recArg = recIt.next();
    VarReplacement vr(recArg.var(), termArg);
    List<Term*>::push(vr.transform(stepArg.term()), res);
  }

  return res;
}

bool InductionHelper::checkAllContained(List<Term*>* lst1, List<Term*>* lst2)
{
  List<Term*>::Iterator it1(lst1);
  while (it1.hasNext()) {
    auto t1 = it1.next();
    // cout << "Checking for containment of " << t1->toString() << endl;
    List<Term*>::Iterator it2(lst2);
    bool found = false;

    while (it2.hasNext()) {
      auto t2 = it2.next();
      // cout << "with " << t2->toString() << endl;
      if (t2->containsSubterm(TermList(t1))) {
        // cout << "contained!" << endl;
        found = true;
        break;
      }
    }
    if (!found) {
      return false;
    }
  }
  return true;
}

} // Shell
