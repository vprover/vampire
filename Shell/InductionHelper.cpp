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
  DArray<TermList> args(other->arity());
  Term::Iterator argIt(other);
  unsigned j = 0;
  while (argIt.hasNext()) {
    auto t = argIt.next();
    if (t.isTerm()) {
      args[j] = TermList(copyTerm(argIt.next().term()));
    } else {
      args[j] = TermList(t.var(), !t.isOrdinaryVar());
    }
    j++;
  }
  return Term::createNonShared(other, args.begin());
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
    str = "((";
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
  str+=_step.toString()+")";
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
  while (rIt.hasNext()) {
    str+=rIt.next().toString();
    if (rIt.hasNext()) {
      str+=" & ";
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
          cout << t2.toString() << " properly contains " << t1.toString() << endl;
        } else {
          cout << t2.toString() << " does not properly contain " << t1.toString() << endl;
        }
        i++;
      }
    }
  }
}

InductionScheme::InductionScheme(Term* t, InductionTemplate* templ)
  : _t(t),
    _templ(templ)
{}

Term* InductionScheme::getTerm() const
{
  return _t;
}

InductionTemplate* InductionScheme::getTemplate() const
{
  return _templ;
}

vstring InductionScheme::toString() const
{
  vstring str;
  str+="Term: "+_t->toString()+
    +"\nScheme: "+_templ->toString();
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
    cout << lhterm->toString() << " " << rhs->toString() << endl;

    InductionTemplate* templ = new InductionTemplate();
    TermList term(lhterm);
    processBody(*rhs, term, templ);
    templ->postprocess();

    cout << "Recursive function: " << lit->toString() << " functor " << lhterm->functor()
         << ", predicate " << isPred << ", with induction template: " << templ->toString() << endl;
    env.signature->addInductionTemplate(lhterm->functor(), isPred, templ);
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
  if (!term->isSpecial()) {
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

      if (copiedHeader->args()[index].isVar()) {
        copiedHeader->args()[index] = *pattern;
      } else {
        Substitution subst;
        subst.bind(matchedVar, pattern->term());
        SubstHelper::apply(copiedHeader->args()[index].term(), subst);
      }
      TermList t(copiedHeader);
      processBody(*matchBody, t, templ);
    }
  } else if (term->isFormula()) {
    auto formula = term->getSpecialData()->getFormula();
    switch (formula->connective()) {
      case LITERAL: {
        TermList lit(formula->literal());
        processBody(lit, header, templ);
        break;
      }
      case TRUE:
      case FALSE: {
        RDescription desc(nullptr, header, nullptr);
        templ->addRDescription(desc);
        break;
      }
      case BOOL_TERM:
      case IFF:
      case FORALL:
      case EXISTS:
#if VDEBUG
      default:
        ASSERTION_VIOLATION;
#endif
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

  Term::Iterator it(term);
  while (it.hasNext()) {
    auto n = it.next();
    processCase(recFun, n, recursiveCalls);
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

} // Shell
