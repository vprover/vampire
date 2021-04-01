/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "InductionPreprocessor.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "FunctionDefinitionDiscovery.hpp"

using namespace Kernel;

namespace Shell {

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

ostream& operator<<(ostream& out, const InductionTemplate::Branch& branch)
{
  if (!branch._recursiveCalls.empty()) {
    out << "(";
    unsigned n = 0;
    for (const auto& r : branch._recursiveCalls) {
      out << r;
      if (++n < branch._recursiveCalls.size()) {
        out << " & ";
      }
    }
    out << ") => ";
  }
  out << branch._header;
  return out;
}

bool InductionTemplate::findVarOrder(
  const vvector<vvector<VarType>>& relations,
  const vset<unsigned>& candidates,
  VarOrder& res)
{
  if (relations.empty()) {
    return true;
  }
  if (candidates.empty()) {
    return false;
  }
  // Split original candidate sets into sets that change together
  // with a bool variable for each to denote whether the set changes in at
  // least one relation (otherwise the set is not a true candidate)
  vset<vset<unsigned>> candidateSets;
  candidateSets.insert(candidates);
  for (const auto& r : relations) {
    vset<unsigned> subterm;
    vset<unsigned> fixed;
    for (unsigned i = 0; i < r.size(); i++) {
      if (r[i] == VarType::FIXED) {
        fixed.insert(i);
      } else if (r[i] == VarType::SUBTERM) {
        subterm.insert(i);
      }
    }
    vset<vset<unsigned>> newCandidateSets;
    for (const auto& c : candidateSets) {
      vset<unsigned> sti, fi;
      // Take intersections of current simultaneously changing
      // or fixed sets with ones that change together in another
      // relation. The result will be non-empty sets which change
      // together or remain fixed together in all relations
      set_intersection(c.begin(), c.end(), subterm.begin(), subterm.end(), inserter(sti, sti.end()));
      set_intersection(c.begin(), c.end(), fixed.begin(), fixed.end(), inserter(fi, fi.end()));
      if (!sti.empty()) {
        newCandidateSets.insert(sti); // set changed variable to true
      }
      if (!fi.empty()) {
        newCandidateSets.insert(fi);
      }
    }
    candidateSets = newCandidateSets;
  }
  for (const auto& c : candidateSets) {
    // The remaining relations are the ones where
    // the selected candidate sets are fixed, otherwise
    // the order is established by the selected set
    vvector<vvector<VarType>> remainingRelations;
    for (const auto r : relations) {
      // we can check only the first of the set
      // because they are all fixed in the same relations
      if (r[*c.begin()] == VarType::FIXED) {
        remainingRelations.push_back(r);
      }
    }
    vset<unsigned> remainingCandidates;
    set_difference(candidates.begin(), candidates.end(),
      c.begin(), c.end(),
      inserter(remainingCandidates, remainingCandidates.end()));
    VarOrder temp = res;
    temp.push_back(c);
    if (findVarOrder(remainingRelations, remainingCandidates, temp)) {
      res = temp;
      return true;
    }
  }
  return false;
}

bool InductionTemplate::checkWellDefinedness(vvector<vvector<TermList>>& missingCases)
{
  missingCases.clear();
  auto arity = _branches[0]._header.term()->arity();
  if (arity == 0) {
    return true;
  }
  if (_branches.empty()) {
    return false;
  }
  unsigned var = 0;
  vvector<vvector<TermList>> availableTermsEmpty;
  for (unsigned i = 0; i < arity; i++) {
    vvector<TermList> v;
    v.push_back(TermList(var++, false));
    availableTermsEmpty.push_back(v);
  }
  vvector<vvector<vvector<TermList>>> availableTermsLists;
  availableTermsLists.push_back(availableTermsEmpty);

  bool overdefined = false;
  for (auto& b : _branches) {
    vvector<vvector<vvector<TermList>>> nextAvailableTermsLists;
    Term::Iterator it(b._header.term());
    unsigned j = 0;
    while (it.hasNext()) {
      auto arg = it.next();
      bool excluded = false;
      if (arg.isTerm()) {
        auto tempLists = availableTermsLists;
        for (auto& availableTerms : tempLists) {
          if (TermAlgebra::excludeTermFromAvailables(availableTerms[j], arg, var)) {
            excluded = true;
          }
        }
        nextAvailableTermsLists.insert(nextAvailableTermsLists.end(),
          tempLists.begin(), tempLists.end());
      } else {
        for (const auto& availableTerms : availableTermsLists) {
          if (!availableTerms[j].empty()) {
            excluded = true;
            break;
          }
        }
      }
      if (!excluded) {
        overdefined = true;
      }
      j++;
    }
    availableTermsLists = nextAvailableTermsLists;
  }

  for (const auto& availableTerms : availableTermsLists) {
    bool valid = true;
    vvector<vvector<TermList>> argTuples(1);
    for (const auto& v : availableTerms) {
      if (v.empty()) {
        valid = false;
        break;
      }
      for (const auto& e : v) {
        vvector<vvector<TermList>> temp;
        for (auto a : argTuples) {
          a.push_back(e);
          temp.push_back(a);
        }
        argTuples = temp;
      }
    }
    if (valid) {
      missingCases.insert(missingCases.end(),
        argTuples.begin(), argTuples.end());
    }
  }
  return !overdefined && missingCases.empty();
}

void InductionTemplate::addMissingCases(const vvector<vvector<TermList>>& missingCases)
{
  auto mainTerm = _branches.begin()->_header.term();
  auto fn = mainTerm->functor();
  auto arity = mainTerm->arity();
  bool isPred = mainTerm->isLiteral();

  env.beginOutput();
  env.out() << "% Warning: adding missing cases ";
  for (const auto& m : missingCases) {
    Stack<TermList> args;
    ASS_EQ(m.size(),arity);
    for(const auto& arg : m) {
      args.push(arg);
    }
    TermList t;
    if (isPred) {
      t = TermList(Literal::create(static_cast<Literal*>(mainTerm), args.begin()));
    } else {
      t = TermList(Term::create(fn, arity, args.begin()));
    }
    env.out() << t << ", ";
    _branches.emplace_back(t);
  }
  env.out() << "to template " << *this << endl;
  env.endOutput();
}

bool InductionTemplate::checkUsefulness()
{
  CALL("InductionTemplate::checkUsefulness");

  // discard whenever:
  // (1) no r-descriptions or
  // (2) no terms in any argument positions or
  // (3) no recursive calls
  bool discard = true;
  for (auto& b : _branches) {
    Term::Iterator argIt(b._header.term());
    if (!b._recursiveCalls.empty()) {
      discard = false;
    }
    while (argIt.hasNext()) {
      auto arg = argIt.next();
      if (arg.isTerm()) {
        discard = false;
      }
    }
  }
  if (discard) {
    auto t = _branches.begin()->_header.term();
    if (env.options->showInduction()) {
      env.beginOutput();
      env.out() << "% Warning: template for "
                << (t->isLiteral() ? "predicate " : "function ")
                << (t->isLiteral() ? static_cast<Literal*>(t)->predicateName() : t->functionName())
                << " is discarded because it is not useful" << endl;
      env.endOutput();
    }
  }
  return !discard;
}

bool InductionTemplate::checkWellFoundedness()
{
  CALL("InductionTemplate::checkWellFoundedness");

  if (_branches.empty()) {
    return true;
  }

  // fill in bit vector of induction variables
  auto arity = _branches[0]._header.term()->arity();
  _inductionVariables = vvector<bool>(arity, false);
  vset<unsigned> candidatePositions;
  vvector<vvector<VarType>> relations;
  for (auto& b : _branches) {
    for (auto& r : b._recursiveCalls) {
      vvector<VarType> relation(arity, VarType::OTHER);
      Term::Iterator argIt1(r.term());
      Term::Iterator argIt2(b._header.term());
      unsigned i = 0;
      while (argIt1.hasNext()) {
        auto t1 = argIt1.next();
        auto t2 = argIt2.next();
        if (t1 == t2) {
          relation[i] = VarType::FIXED;
        } else if (t2.isTerm() && t2.term()->shared()
                   && (t1.isVar() || t1.term()->shared())
                   && t2.containsSubterm(t1)) {
          relation[i] = VarType::SUBTERM;
          candidatePositions.insert(i);
          _inductionVariables[i] = true;
        } else {
          candidatePositions.insert(i);
        }
        i++;
      }
      relations.push_back(relation);
    }
  }
  _order.clear();
  if (!findVarOrder(relations, candidatePositions, _order)) {
    _order.clear();
    _order.push_back(candidatePositions);
    for (const auto& o : _order) {
      for (const auto& i : o) {
        _inductionVariables[i] = true;
      }
    }
    return false;
  }
  return true;
}

ostream& operator<<(ostream& out, const InductionTemplate& templ)
{
  out << "Branches: ";
  unsigned n = 0;
  for (const auto& b : templ._branches) {
    out << b;
    if (++n < templ._branches.size()) {
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
  out << ") and variable order (";
  for (const auto& r : templ._order) {
    if (r.size() == 1) {
      out << *r.begin() << ",";
    } else {
      out << "{";
      for (const auto& v : r) {
        out << v << ",";
      }
      out << "},";
    }
  }
  out << ")";
  return out;
}

void parseRecursiveDefinition(Literal* lit)
{
  CALL("parseRecursiveDefinition");

  auto lhs = lit->isFunctionOrientedReversed() ? lit->nthArgument(1) : lit->nthArgument(0);
  auto rhs = lit->isFunctionOrientedReversed() ? lit->nthArgument(0) : lit->nthArgument(1);
  auto lhterm = lhs->term();
  bool isPred = lhterm->isFormula();
  if (isPred) {
    lhterm = lhterm->getSpecialData()->getFormula()->literal();
  }

  InductionTemplate templ;
  TermList term(lhterm);
  InductionPreprocessor::processBody(*rhs, term, templ);
  if (!templ.checkUsefulness()) {
    return;
  }
  templ.checkWellFoundedness();
  vvector<vvector<TermList>> missingCases;
  if (!templ.checkWellDefinedness(missingCases) && !missingCases.empty()) {
    templ.addMissingCases(missingCases);
  }

  if(env.options->showInduction()){
    env.beginOutput();
    env.out() << "[Induction] function: " << *lit << endl << ", with induction template: " << templ << endl;
    env.endOutput();
  }
  env.signature->addInductionTemplate(lhterm->functor(), isPred, std::move(templ));
}

void InductionPreprocessor::preprocessProblem(Problem& prb)
{
  CALL("InductionPreprocessor::preprocessProblem");

  FunctionDefinitionDiscovery d;
  UnitList::Iterator it(prb.units());
  while (it.hasNext()) {
    auto unit = it.next();
    if (unit->isClause()){
      continue;
    }

    auto formula = unit->getFormula();
    while (formula->connective() == Connective::FORALL) {
      formula = formula->qarg();
    }

    if (formula->connective() == Connective::LITERAL
        && formula->literal()->isFunctionDefinition()) {
      parseRecursiveDefinition(formula->literal());
    } else if (env.options->functionDefinitionDiscovery()) {
      d.findPossibleRecursiveDefinitions(formula);
    }
  }
  d.addBestConfiguration();
}

void processCase(const unsigned recFun, const bool isPred, TermList body, vvector<TermList>& recursiveCalls)
{
  CALL("processCase");

  // If we arrived at a variable, nothing to do
  if (!body.isTerm()) {
    return;
  }

  // Check if this term is a recursive call, store it
  auto term = body.term();
  if (term->functor() == recFun && isPred == term->isFormula()) {
    recursiveCalls.push_back(body);
  }

  // Otherwise recurse into the subterms/subformulas
  if (term->isFormula()) {
    auto formula = term->getSpecialData()->getFormula();
    switch (formula->connective()) {
      case LITERAL: {
        TermList lit(formula->literal());
        processCase(recFun, isPred, lit, recursiveCalls);
        break;
      }
      case BOOL_TERM: {
        processCase(recFun, isPred, formula->getBooleanTerm(), recursiveCalls);
        break;
      }
      case AND:
      case OR: {
        FormulaList::Iterator it(formula->args());
        while (it.hasNext()) {
          // TODO(mhajdu): maybe don't create a new Term here
          TermList ft(Term::createFormula(it.next()));
          processCase(recFun, isPred, ft, recursiveCalls);
        }
        break;
      }
      case IFF:
      case XOR:
      case IMP: {
        break;
      }
      case TRUE:
      case FALSE: {
        break;
      }
      case FORALL:
      case EXISTS: {
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
      processCase(recFun, isPred, n, recursiveCalls);
    }
  }
}

void InductionPreprocessor::processFormulaBody(Formula* body, Literal* header, InductionTemplate& templ)
{
  CALL("InductionPreprocessor::processFormulaBody");

  switch(body->connective()) {
    case LITERAL: {
      auto lit = body->literal();
      vvector<TermList> recCalls;
      if (lit->isEquality()) {
        processCase(header->functor(), header->isFormula(), *lit->nthArgument(0), recCalls);
        processCase(header->functor(), header->isFormula(), *lit->nthArgument(1), recCalls);
      } else {
        processCase(header->functor(), header->isFormula(), TermList(lit), recCalls);
      }
      templ._branches.emplace_back(recCalls, TermList(header));
      break;
    }
    case BOOL_TERM: {
      vvector<TermList> recCalls;
      processCase(header->functor(), header->isFormula(), body->getBooleanTerm(), recCalls);
      templ._branches.emplace_back(recCalls, TermList(header));
      break;
    }
    case AND:
    case OR: {
      FormulaList::Iterator it(body->args());
      while (it.hasNext()) {
        auto arg = it.next();
        processFormulaBody(arg, header, templ);
      }
      break;
    }
    case FALSE:
    case TRUE: {
      templ._branches.emplace_back(TermList(header));
      break;
    }
    case NOT: {
      processFormulaBody(body->uarg(), header, templ);
      break;
    }
    case IMP:
    case IFF:
    case XOR: {
      processFormulaBody(body->left(), header, templ);
      processFormulaBody(body->right(), header, templ);
      break;
    }
    case FORALL:
    case EXISTS:
    case NAME:
    case NOCONN: {
      break;
    }
  }
}

void InductionPreprocessor::processBody(TermList body, TermList header, InductionTemplate& templ)
{
  CALL("InductionPreprocessor::processBody");

  // Base case
  if (body.isVar()) {
    templ._branches.emplace_back(header);
    return;
  }
  // Possibly recursive case
  auto term = body.term();
  if (!term->isSpecial() || term->isFormula()) {
    vvector<TermList> recursiveCalls;
    processCase(header.term()->functor(), header.term()->isFormula(), body, recursiveCalls);
    templ._branches.emplace_back(recursiveCalls, header);
    return;
  }
  // TODO(mhajdu): Here there can be other constructs e.g. ITE, process them
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
      processBody(*matchBody, t, templ);
    }
  }
  else if (term->isITE())
  {
    processBody(*term->nthArgument(0), header, templ);
    processBody(*term->nthArgument(1), header, templ);
  }
}

} // Shell
