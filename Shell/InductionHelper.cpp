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

RecursiveCase::RecursiveCase(List<TermList>* hypotheses, TermList step)
  : _hypotheses(hypotheses),
    _step(step)
{}

Lib::vstring RecursiveCase::toString() const
{
  Lib::vstring str = "((";
  List<TermList>::Iterator it(_hypotheses);
  while (it.hasNext()) {
    str+=it.next().toString();
    if (it.hasNext()) {
      str+=" & ";
    }
  }
  str+=") => "+_step.toString()+")";
  return str;
}

InductionScheme::InductionScheme()
  : _baseCases(0),
    _recursiveCases(0)
{}

void InductionScheme::addBaseCase(TermList c)
{
  List<TermList>::push(c, _baseCases);
}

void InductionScheme::addRecursiveCase(RecursiveCase c)
{
  List<RecursiveCase>::push(c, _recursiveCases);
}

Lib::vstring InductionScheme::toString() const
{
  Lib::vstring str;
  List<TermList>::Iterator baseIt(_baseCases);
  while (baseIt.hasNext()) {
    str+=baseIt.next().toString()+" & ";
  }
  List<RecursiveCase>::Iterator recIt(_recursiveCases);
  while (recIt.hasNext()) {
    str+=recIt.next().toString();
    if (baseIt.hasNext()) {
      str+=" & ";
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
    ASS(!lhterm->isSpecial());

    vvector<TermList> args;
    Term::Iterator argit(lhterm);
    while (argit.hasNext()) {
        auto arg = argit.next();
        args.push_back(arg);
    }
    InductionScheme* scheme = new InductionScheme();
    processBody(*rhs, *lhs, scheme);
    
    cout << "Recursive function: " << lit->toString()
         << ", with induction scheme: " << scheme->toString() << endl;
    env.signature->addInductionScheme(lhterm->functor(), scheme);
  }
}

void InductionHelper::processBody(TermList& body, TermList& header, InductionScheme*& scheme)
{
  if (body.isVar()) {
    scheme->addBaseCase(header);
    return;
  }
  auto term = body.term();
  if (!term->isSpecial()) {
    List<TermList>* hypotheses(0);
    if (processCase(header.term()->functor(), body, hypotheses)) {
      scheme->addRecursiveCase(RecursiveCase(hypotheses, header));
    } else {
      scheme->addBaseCase(header);
    }
  } else if (term->isMatch()) {
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
      processBody(*matchBody, t, scheme);
    }
  }
}

// returns true if the case is recursive
bool InductionHelper::processCase(const unsigned recFun, TermList& body, List<TermList>*& hypotheses)
{
  if (!body.isTerm()) {
    return false;
  }

  auto term = body.term();
  if (term->functor() == recFun) {
    List<TermList>::push(body, hypotheses);
    // TODO(mhajdu): recursive calls in args? 
    return true;
  }

  Term::Iterator it(term);
  bool recursive = false;
  while (it.hasNext()) {
    auto n = it.next();
    if (processCase(recFun, n, hypotheses)) {
      recursive = true;
    }
  }
  return recursive;
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
