/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include <set>

#include "FunctionDefinitionHandler.hpp"
#include "Inferences/InductionHelper.hpp"

#include "Kernel/FormulaUnit.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Problem.hpp"

#include "Lib/SharedSet.hpp"

using namespace Inferences;
using namespace Kernel;
using namespace Lib;
using namespace std;

namespace Shell {

bool canBeUsedForRewriting(Term* lhs, Clause* cl)
{
  // TODO: we are using a codetree to get the generalizations
  // for rewriting and it cannot handle unbound variables on
  // the indexed side, hence we check if there are any variables
  // that would be unbound
  auto vIt = cl->getVariableIterator();
  while (vIt.hasNext()) {
    auto v = vIt.next();
    if (!lhs->containsSubterm(TermList(v,false))) {
      return false;
    }
  }
  return true;
}

Literal* replaceDefinition(Literal* lit)
{
  unsigned orig_fn;
  if (env.signature->isBoolDefPred(lit->functor(), orig_fn)) {
    TermStack args;
    for (unsigned i = 0; i < lit->arity(); i++) {
      args.push(*lit->nthArgument(i));
    }
    return Literal::create(orig_fn, lit->arity(), lit->polarity(), args.begin());
  } else if (env.signature->isFnDefPred(lit->functor())) {
    ASS(env.signature->isFnDefPred(lit->functor()));
    auto lhs = lit->termArg(0);
    ASS(lhs.isTerm());
    return Literal::createEquality(lit->polarity(), lhs, lit->termArg(1), SortHelper::getResultSort(lhs.term()));
  }
  return lit;
}

void FunctionDefinitionHandler::initAndPreprocessEarly(Problem& prb)
{
  UnitList::RefIterator it(prb.units());
  while (it.hasNext()) {
    auto u = it.next();
    if (u->isClause()) {
      auto cl = u->asClause();
      for (unsigned i = 0; i < cl->length(); i++) {
        (*cl)[i] = replaceDefinition((*cl)[i]);
      }
    } else {
      auto f = static_cast<FormulaUnit*>(u)->formula();
      SubformulaIterator sfit(f);
      while (sfit.hasNext()) {
        auto f = sfit.next();
        if (f->connective()==Connective::LITERAL) {
          static_cast<AtomicFormula*>(f)->setLiteral(replaceDefinition(static_cast<AtomicFormula*>(f)->getLiteral()));
        }
      }
    }
  }
}

void FunctionDefinitionHandler::initAndPreprocessLate(Problem& prb,const Options& opts)
{
  // reset state
  _is = new CodeTreeTIS<TermLiteralClause>();
  _templates.reset();

  UnitList::DelIterator it(prb.units());
  while (it.hasNext()) {
    auto u = it.next();
    ASS(u->isClause());
    auto cl = u->asClause();
    LiteralStack defLits;
    LiteralStack condLits;
    for (unsigned i = 0; i < cl->length(); i++) {
      auto lit = (*cl)[i];
      unsigned p;
      if (env.signature->isFnDefPred(lit->functor()) || env.signature->isBoolDefPred(lit->functor(), p)) {
        defLits.push(lit);
      } else {
        condLits.push(lit);
      }
    }

    // clause not from a definition
    if (defLits.isEmpty()) {
      continue;
    }

    // clause contains definitions, we need to replace them with equalities
    auto lits = condLits;
    for (const auto& lit : defLits) {
      lits.push(replaceDefinition(lit));
    }
    Clause* defCl = Clause::fromStack(lits, NonspecificInference1(InferenceRule::DEFINITION_UNFOLDING,u));

    // multiple defining equations inside clause, skip
    if (defLits.size()!=1) {
      it.replace(defCl);
      continue;
    }

    if (env.signature->isFnDefPred(defLits[0]->functor())) {
      auto lhs = defLits[0]->termArg(0);
      auto rhs = defLits[0]->termArg(1);

      // process for induction
      addFunctionBranch(lhs.term(), rhs);

      // process for rewriting
      if (opts.functionDefinitionRewriting() && canBeUsedForRewriting(lhs.term(), defCl)) {
        it.del(); // take ownership
        defCl->setSplits(SplitSet::getEmpty());
        defCl->incRefCnt();
        ASS_EQ(condLits.size()+1,lits.size());
        _is->insert(TermLiteralClause {lhs.term(), lits.top(), defCl});
        // TODO should we store this clause anywhere else?
      } else {
        it.replace(defCl);
      }
    } else {
      addPredicateBranch(Literal::positiveLiteral(lits.top()), condLits);
      it.replace(defCl);
    }
  }

  DHMap<pair<unsigned,SymbolType>,RecursionTemplate>::DelIterator tIt(_templates);
  while (tIt.hasNext()) {
    auto k = tIt.nextKey();
    auto ptr = _templates.findPtr(k);
    if (!ptr->finalize()) {
      tIt.del();
      continue;
    }
    if (opts.showInduction()) {
      cout << "[Induction] added induction template: " << ptr->toString() << endl;
    }
  }
}

void FunctionDefinitionHandler::addFunctionBranch(Term* header, TermList body)
{
  auto fn = header->functor();
  RecursionTemplate* templ;
  _templates.getValuePtr(make_pair(fn,SymbolType::FUNC), templ, RecursionTemplate(header));

  // handle for induction
  std::vector<Term*> recursiveCalls;
  if (body.isTerm()) {
    NonVariableNonTypeIterator it(body.term(), true);
    while (it.hasNext()) {
      auto st = it.next();
      if (st->functor() == fn) {
        recursiveCalls.push_back(st);
      }
    }
  }
  templ->addBranch(std::move(recursiveCalls), header);
}

void FunctionDefinitionHandler::addPredicateBranch(Literal* header, const LiteralStack& conditions)
{
  auto fn = header->functor();
  RecursionTemplate* templ;
  _templates.getValuePtr(make_pair(fn,SymbolType::PRED), templ, RecursionTemplate(header));

  // handle for induction
  std::vector<Term*> recursiveCalls;
  ASS(static_cast<Literal*>(header)->isPositive());
  for(const auto& lit : conditions) {
    if (!lit->isEquality() && fn == lit->functor()) {
      recursiveCalls.push_back(lit->isPositive() ? lit : Literal::complementaryLiteral(lit));
    }
  }
  templ->addBranch(std::move(recursiveCalls), header);
}

const InductionTemplate* FunctionDefinitionHandler::matchesTerm(Term* t, Stack<Term*>& inductionTerms) const
{
  if (!InductionHelper::isStructInductionOn()) {
    return nullptr;
  }
  auto rtempl = getRecursionTemplate(t);
  if (!rtempl) {
    return nullptr;
  }

  inductionTerms.reset();
  for (unsigned i = 0; i < t->arity(); i++) {
    if (!rtempl->inductionPositions()[i]) {
      continue;
    }
    auto arg = *t->nthArgument(i);
    if (arg.isVar()) {
      return nullptr;
    }
    auto argT = arg.term();
    if (!InductionHelper::isInductionTerm(argT) ||
        !InductionHelper::isStructInductionTerm(argT)) {
      return nullptr;
    }
    auto it = std::find(inductionTerms.begin(),inductionTerms.end(),argT);
    if (it != inductionTerms.end()) {
      return nullptr;
    }
    inductionTerms.push(argT);
  }
  if (inductionTerms.isEmpty()) {
    return nullptr;
  }
  return rtempl->templ();
}

bool RecursionTemplate::finalize()
{
  if (!checkWellFoundedness() || !checkUsefulness()) {
    return false;
  }

  checkWellDefinedness();

  auto indPos = Stack<unsigned>::fromIterator(range(0,_arity).filter([&](unsigned i) { return _indPos[i]; }));

  // first create normalized sorts
  TermStack sorts;
  Renaming r;
  for (unsigned i : indPos) {
    r.normalizeVariables(_type->arg(i));
    sorts.push(r.apply(_type->arg(i)));
  }

  unsigned var = r.nextVar();
  Stack<InductionCase> cases;
  // fill out InductionTemplate
  for (const auto& b : _branches) {
    // we need this sophisticated renaming due to
    // already fixed sort variables coming from _type
    static DHMap<unsigned,unsigned> renaming;
    renaming.reset();
    auto renameTerm = [&](TermList t, TermList sort) {
      if (t.isVar()) {
        unsigned* ptr;
        if (renaming.getValuePtr(t.var(), ptr)) {
          *ptr = var++;
        }
        return TermList::var(*ptr);
      } else {
        auto tsort = SortHelper::getResultSort(t.term());
        Substitution binder;
        ALWAYS(MatchingUtils::matchTerms(tsort, sort, binder));
        iterTraits(binder.items()).forEach([&](const auto& kv) {
          ASS(kv.second.isVar());
          renaming.insert(kv.first,kv.second.var());
        });
        iterTraits(VariableIterator(t)).forEach([&](TermList v) {
          unsigned* ptr;
          if (renaming.getValuePtr(v.var(), ptr)) {
            *ptr = var++;
          }
        });
        struct Applicator {
          TermList apply(unsigned var) { return TermList::var(renaming.get(var)); }
        } appl;
        return SubstHelper::apply(t, appl);
      }
    };
    TermStack conclusion;
    for (unsigned i = 0; i < indPos.size(); i++) {
      conclusion.push(renameTerm(*b._header->nthArgument(indPos[i]), sorts[i]));
    }
    Stack<InductionUnit> hypotheses;
    for (const auto& recCall : b._recursiveCalls) {
      TermStack hyp;
      for (unsigned i = 0; i < indPos.size(); i++) {
        hyp.push(renameTerm(*recCall->nthArgument(indPos[i]), sorts[i]));
      }
      hypotheses.emplace(std::move(hyp));
    }
    cases.emplace(std::move(conclusion), std::move(hypotheses));
  }
  _templ = make_unique<const InductionTemplate>(
    std::move(sorts),
    std::move(cases),
    InductionUnit(TermStack::fromIterator(range(0,indPos.size()).map([&](unsigned i) { return TermList::var(var++); }))),
    /*maxVar=*/var,
    InferenceRule::STRUCT_INDUCTION_AXIOM_RECURSION
  );
  return true;
}

void RecursionTemplate::checkWellDefinedness()
{
  std::vector<Term*> cases;
  for (auto& b : _branches) {
    cases.push_back(b._header);
  }
  std::vector<std::vector<TermList>> missingCases;
  InductionPreprocessor::checkWellDefinedness(cases, missingCases);

  if (!missingCases.empty()) {
    if (env.options->showInduction()) {
      cout << "% Warning: adding missing cases to template " << toString();
    }
    for (const auto& m : missingCases) {
      Stack<TermList> args;
      ASS_EQ(m.size(), _arity);
      for(const auto& arg : m) {
        args.push(arg);
      }
      Term* t;
      if (_isLit) {
        t = Literal::create(static_cast<Literal*>(_branches[0]._header), args.begin());
      } else {
        t = Term::create(_functor, _arity, args.begin());
      }
      addBranch(std::vector<Term*>(), Renaming::normalize(t));
    }
    if (env.options->showInduction()) {
      cout << ". New template is " << toString() << endl;
    }
  }
}

bool RecursionTemplate::Branch::contains(const RecursionTemplate::Branch& other) const
{
  RobSubstitution subst;
  if (!subst.match(TermList(_header), 0, TermList(other._header), 1)) {
    return false;
  }

  for (auto recCall2 : other._recursiveCalls) {
    bool found = false;
    for (auto recCall1 : _recursiveCalls) {
      Term* l1;
      Term* l2;
      if (_header->isLiteral()) {
        l1 = subst.apply(static_cast<Literal*>(recCall1), 0);
        l2 = subst.apply(static_cast<Literal*>(recCall2), 1);
      } else {
        l1 = subst.apply(TermList(recCall1), 0).term();
        l2 = subst.apply(TermList(recCall2), 1).term();
      }
      if (l1 == l2) {
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

bool RecursionTemplate::checkUsefulness() const
{
  // discard templates without inductive argument positions:
  // this happens either when there are no recursive calls
  // or none of the arguments change in any recursive call
  bool discard = true;
  for (const auto& p : _indPos) {
    if (p) {
      discard = false;
    }
  }
  return !discard;
}

bool RecursionTemplate::checkWellFoundedness()
{
  std::vector<pair<Term*, Term*>> relatedTerms;
  for (auto& b : _branches) {
    for (auto& r : b._recursiveCalls) {
      relatedTerms.push_back(make_pair(b._header, r));

      // fill in bit vector of induction variables
      for (unsigned i = 0; i < _arity; i++) {
        if (env.signature->isTermAlgebraSort(_type->arg(i))) {
          _indPos[i] = _indPos[i] || (*b._header->nthArgument(i) != *r->nthArgument(i));
        }
      }
    }
  }
  return InductionPreprocessor::checkWellFoundedness(relatedTerms);
}

RecursionTemplate::RecursionTemplate(const Term* t)
  : _functor(t->functor()), _arity(t->arity()), _isLit(t->isLiteral()),
  _type(_isLit ? env.signature->getPredicate(_functor)->predType()
               : env.signature->getFunction(_functor)->fnType()),
  _branches(), _indPos(_arity, false) {}

void RecursionTemplate::addBranch(std::vector<Term*>&& recursiveCalls, Term* header)
{
  ASS(header->arity() == _arity && header->isLiteral() == _isLit && header->functor() == _functor);
  Branch branch(std::move(recursiveCalls), std::move(header));
  for (auto b : _branches) {
    if (b.contains(branch)) {
      return;
    }
  }
  _branches.erase(remove_if(_branches.begin(), _branches.end(),
  [&branch](const Branch& b) {
    return branch.contains(b);
  }), _branches.end());
  _branches.push_back(std::move(branch));
}

std::string RecursionTemplate::toString() const
{
  std::stringstream str;
  str << "Branches: ";
  unsigned n = 0;
  for (const auto& b : _branches) {
    if (!b._recursiveCalls.empty()) {
      str << "(";
      unsigned n = 0;
      for (const auto& r : b._recursiveCalls) {
        str << *r;
        if (++n < b._recursiveCalls.size()) {
          str << " & ";
        }
      }
      str << ") => ";
    }
    str << *b._header;
    if (++n < _branches.size()) {
      str << "; ";
    }
  }
  str << " with positions: (";
  for (unsigned i = 0; i < _arity; i++) {
    if (_indPos[i]) {
      str << "i";
    } else {
      str << "0";
    }
    if (i+1 < _arity) {
      str << ",";
    }
  }
  str << ")";
  return str.str();
}

/**
 * Try to find a lexicographic order between the arguments
 * by exhaustively trying all combinations.
 */
bool checkWellFoundednessHelper(const std::vector<pair<Term*,Term*>>& relatedTerms,
  const std::set<unsigned>& indices, const std::set<unsigned>& positions)
{
  if (indices.empty()) {
    return true;
  }
  if (positions.empty()) {
    return false;
  }
  for (const auto& p : positions) {
    std::set<unsigned> newInd;
    bool canOrder = true;
    for (const auto& i : indices) {
      auto arg1 = *relatedTerms[i].first->nthArgument(p);
      auto arg2 = *relatedTerms[i].second->nthArgument(p);
      if (arg1 == arg2) {
        newInd.insert(i);
      } else if (!arg1.containsSubterm(arg2)) {
        canOrder = false;
        break;
      }
    }
    if (canOrder) {
      auto newPos = positions;
      newPos.erase(p);
      if (checkWellFoundednessHelper(relatedTerms, newInd, newPos)) {
        return true;
      }
    }
  }
  return false;
}

bool InductionPreprocessor::checkWellFoundedness(const std::vector<pair<Term*,Term*>>& relatedTerms)
{
  if (relatedTerms.empty()) {
    return true;
  }
  auto t = relatedTerms[0].first;
  bool isFun = !t->isLiteral();
  auto fn = t->functor();
  auto arity = t->arity();
  OperatorType* type;
  if (isFun) {
    type = env.signature->getFunction(fn)->fnType();
  } else {
    type = env.signature->getPredicate(fn)->predType();
  }
  std::set<unsigned> positions;
  for (unsigned i = 0; i < arity; i++) {
    if (env.signature->isTermAlgebraSort(type->arg(i))) {
      positions.insert(i);
    }
  }
  std::set<unsigned> indices;
  for (unsigned i = 0; i < relatedTerms.size(); i++) {
    indices.insert(i);
  }
  return checkWellFoundednessHelper(relatedTerms, indices, positions);
}

/**
 * Check well-definedness for term algebra arguments and
 * in the process generate all missing cases.
 */
bool InductionPreprocessor::checkWellDefinedness(const std::vector<Term*>& cases, std::vector<std::vector<TermList>>& missingCases)
{
  if (cases.empty()) {
    return false;
  }
  missingCases.clear();
  auto arity = cases[0]->arity();
  if (arity == 0) {
    return true;
  }
  Stack<Stack<TermStack>> availableTermsLists;
  availableTermsLists.push(Stack<TermStack>(arity));
  unsigned var = 0;
  for (unsigned i = 0; i < arity; i++) {
    availableTermsLists.top().push(TermStack({ TermList(var++, false) }));
  }

  for (auto& c : cases) {
    Stack<Stack<TermStack>> nextAvailableTermsLists;
    for (unsigned i = 0; i < arity; i++) {
      auto arg = *c->nthArgument(i);
      // we check lazily for non-term algebra sort non-variables
      if (arg.isTerm() && env.signature->isTermAlgebraSort(SortHelper::getResultSort(arg.term()))) {
        auto tempLists = availableTermsLists;
        for (auto& availableTerms : tempLists) {
          TermAlgebra::excludeTermFromAvailables(availableTerms[i], arg, var);
        }
        for (auto&& e : tempLists) {
          nextAvailableTermsLists.push(std::move(e));
        }
      } else {
        for (const auto& availableTerms : availableTermsLists) {
          if (!availableTerms[i].isEmpty()) {
            break;
          }
        }
      }
    }
    availableTermsLists = nextAvailableTermsLists;
  }

  for (const auto& availableTerms : availableTermsLists) {
    bool valid = true;
    std::vector<std::vector<TermList>> argTuples(1);
    for (const auto& v : availableTerms) {
      if (v.isEmpty()) {
        valid = false;
        break;
      }
      std::vector<std::vector<TermList>> temp;
      for (const auto& e : v) {
        for (auto a : argTuples) {
          a.push_back(e);
          temp.push_back(a);
        }
      }
      argTuples = temp;
    }
    if (valid) {
      missingCases.insert(missingCases.end(),
        argTuples.begin(), argTuples.end());
    }
  }
  return missingCases.empty();
}

} // Shell
