/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "FunctionDefinitionHandler.hpp"
#include "Inferences/InductionHelper.hpp"

#include "Kernel/Matcher.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/SubformulaIterator.hpp"

#include "Lib/Hash.hpp"
#include "Lib/SharedSet.hpp"

using namespace Inferences;
using namespace Kernel;
using namespace Lib;

namespace Shell {

void FunctionDefinitionHandler::preprocess(Problem& prb)
{
  CALL("FunctionDefinitionHandler::preprocess(Problem&)");
  UnitList::DelIterator it(prb.units());
  while (it.hasNext()) {
    auto u = it.next();
    if (u->isClause()) {
      continue;
    }
    auto fu = static_cast<FormulaUnit*>(u);
    if (fu->isFunctionDefinition()) {
      // if the definition could be processed and the function axioms
      // will be used as rewrite rules, we remove the unit
      Stack<Branch> branches;
      if (preprocess(fu->formula(), branches)) {
        addFunction(branches, u);
        if (env.options->functionDefinitionRewriting()) {
          it.del();
        }
      }
    }
  }
}

bool FunctionDefinitionHandler::preprocess(Formula* f, Stack<Branch>& branches)
{
  CALL("FunctionDefinitionHandler::preprocess(Formula*, Stack<Branch>& branches)");
  ASS_EQ(f->connective(), LITERAL);

  auto l = f->literal();
  ASS(l->isEquality());

  //TODO handle predicate definitions as well
  ASS(l->nthArgument(0)->isTerm());
  auto header = l->nthArgument(0)->term();
  if (header->isSpecial()) {
    // literal headers are nicely packed into multiple layers
    ASS_EQ(header->getSpecialData()->getType(), Term::SF_FORMULA);
    auto of = header->getSpecialData()->getFormula();
    ASS_EQ(of->connective(), LITERAL);
    header = of->literal();
  }
  Stack<Branch> todos;
  todos.push({
    .header = header,
    .body = *l->nthArgument(1),
    .literals = LiteralStack()
  });
  while (todos.isNonEmpty()) {
    auto b = todos.pop();
    if (b.body.isVar() || !b.body.term()->isSpecial()) {
      branches.push(std::move(b));
      continue;
    }
    auto t = b.body.term();
    Term::SpecialTermData *sd = t->getSpecialData();
    switch (sd->getType()) {
      case Term::SF_FORMULA: {
        // only the atoms of formula bodies of bool
        // functions are interesting, so save them
        ASS(header->isLiteral());
        auto f = sd->getFormula();
        SubformulaIterator sfit(f);
        while(sfit.hasNext()) {
          Formula* sf = sfit.next();
          if(sf->connective()==LITERAL) {
            Literal* l = sf->literal();
            b.literals.push(Literal::positiveLiteral(l));
          }
        }
        // f->collectAtoms(b.literals);
        branches.push(std::move(b));
        break;
      }
      case Term::SF_LET:
      case Term::SF_LET_TUPLE:
      case Term::SF_TUPLE: {
        return false;
      }

      case Term::SF_ITE: {
        auto cf = sd->getCondition();
        switch (cf->connective())
        {
        case LITERAL: {
          auto l = cf->literal();
          todos.push(addCondition(Literal::complementaryLiteral(l), b, *t->nthArgument(0)));
          todos.push(addCondition(l, b, *t->nthArgument(1)));
          break;
        }
        default: {
          return false;
        }
        }
        break;
      }

      case Term::SF_MATCH: {
        auto matched = *t->nthArgument(0);
        for (unsigned int i = 1; i < t->arity(); i += 2) {
          todos.push(substituteBoundVariable(matched.var(), *t->nthArgument(i), b, *t->nthArgument(i+1)));
        }
        break;
      }

      default:
        ASSERTION_VIOLATION_REP(t->toString());
    }
  }
  return true;
}

void FunctionDefinitionHandler::addFunction(const Stack<Branch>& branches, Unit* unit)
{
  CALL("FunctionDefinitionHandler::addFunction");
  ASS_REP(branches.isNonEmpty(), unit->toString());

  auto fn = branches[0].header->functor();
  auto isLit = branches[0].header->isLiteral();
  auto symb = isLit ? env.signature->getPredicate(fn) : env.signature->getFunction(fn);
  auto sort = isLit ? symb->predType()->result() : symb->fnType()->result();
  auto templ = new InductionTemplate(branches[0].header);
  for (auto& b : branches) {
    // handle for induction
    vvector<Term*> recursiveCalls;
    if (isLit) {
      for(const auto& lit : b.literals) {
        if (!lit->isEquality() && fn == lit->functor()) {
          recursiveCalls.push_back(lit->isPositive() ? lit : Literal::complementaryLiteral(lit));
        }
      }
      if (static_cast<Literal*>(b.header)->isNegative()) {
        b.header = Literal::complementaryLiteral(static_cast<Literal*>(b.header));
      }
    } else {
      if (b.body.isTerm()) {
        NonVariableIterator it(b.body.term(), true);
        while (it.hasNext()) {
          auto st = it.next();
          if (st.term()->functor() == fn) {
            recursiveCalls.push_back(st.term());
          }
        }
      }
    }
    templ->addBranch(std::move(recursiveCalls), b.header);

    // handle for rewriting
    if (!isLit && env.options->functionDefinitionRewriting()) {
      auto mainLit = Literal::createEquality(true, TermList(b.header), b.body, sort);
      b.literals.push(mainLit);
      auto rwCl = Clause::fromStack(b.literals, FormulaTransformation(InferenceRule::CLAUSIFY,unit));
      rwCl->setSplits(SplitSet::getEmpty());
      rwCl->incRefCnt();
      _is.insert(TermList(b.header), mainLit, rwCl);
    }
  }
  if (templ->finalize()) {
    if (env.options->showInduction()){
      env.beginOutput();
      env.out() << "[Induction] " << (isLit ? "predicate " : "function ") << symb->name() << endl;
      env.out() << ", with induction template: " << templ->toString() << endl;
      env.endOutput();
    }
    ALWAYS(_templates.insert(make_pair(make_pair(fn,!isLit), templ)).second);
  }
}

FunctionDefinitionHandler::Branch FunctionDefinitionHandler::substituteBoundVariable(unsigned var, TermList t, const Branch& b, TermList body)
{
  Substitution subst;
  subst.bind(var, t);

  auto bn = b;
  bn.body = SubstHelper::apply(body, subst);
  bn.header = SubstHelper::apply(bn.header, subst);
  for (auto& lit : bn.literals) {
    lit = SubstHelper::apply(lit, subst);
  }
  return bn;
}

FunctionDefinitionHandler::Branch FunctionDefinitionHandler::addCondition(Literal* lit, const Branch& b, TermList body)
{
  if (lit->isEquality() && lit->isNegative()) {
    TermList lhs = *lit->nthArgument(0);
    TermList rhs = *lit->nthArgument(1);
    if (lhs.isVar() || rhs.isVar()) {
      if (lhs.isTerm() && rhs.isVar()) {
        swap(lhs,rhs);
      }
      return substituteBoundVariable(lhs.var(), rhs, b, body);
    }
  }
  auto bn = b;
  bn.body = body;
  bn.literals.push(lit);
  return bn;
}

bool InductionTemplate::finalize() {
  CALL("InductionTemplate::finalize");

  if (!checkWellFoundedness() || !checkUsefulness()) {
    return false;
  }

  checkWellDefinedness();
  return true;
}

void InductionTemplate::checkWellDefinedness()
{
  CALL("InductionTemplate::checkWellDefinedness");

  vvector<Term*> cases;
  for (auto& b : _branches) {
    cases.push_back(b._header);
  }
  vvector<vvector<TermList>> missingCases;
  InductionPreprocessor::checkWellDefinedness(cases, missingCases);

  if (!missingCases.empty()) {
    if (env.options->showInduction()) {
      env.beginOutput();
      env.out() << "% Warning: adding missing cases to template " << toString();
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
      addBranch(vvector<Term*>(), std::move(t));
    }
    if (env.options->showInduction()) {
      env.out() << ". New template is " << toString() << endl;
      env.endOutput();
    }
  }
}

bool InductionTemplate::matchesTerm(Term* t, vvector<Term*>& inductionTerms) const
{
  CALL("InductionTemplate::matchesTerm");
  ASS(t->ground());
  inductionTerms.clear();
  for (unsigned i = 0; i < t->arity(); i++) {
    auto arg = t->nthArgument(i)->term();
    auto f = arg->functor();
    if (_indPos[i]) {
      if (!InductionHelper::isInductionTermFunctor(f) ||
          !InductionHelper::isStructInductionOn() ||
          !InductionHelper::isStructInductionTerm(arg)) {
        return false;
      }
      auto it = std::find(inductionTerms.begin(),inductionTerms.end(),arg);
      if (it != inductionTerms.end()) {
        return false;
      }
      inductionTerms.push_back(arg);
    }
  }
  return !inductionTerms.empty();
}

bool InductionTemplate::Branch::contains(const InductionTemplate::Branch& other) const
{
  CALL("InductionTemplate::Branch::contains");

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

bool InductionTemplate::checkUsefulness() const
{
  CALL("InductionTemplate::checkUsefulness");

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

bool InductionTemplate::checkWellFoundedness()
{
  CALL("InductionTemplate::checkWellFoundedness");

  // fill in bit vector of induction variables
  vvector<pair<Term*, Term*>> relatedTerms;
  for (auto& b : _branches) {
    for (auto& r : b._recursiveCalls) {
      relatedTerms.push_back(make_pair(b._header, r));
      for (unsigned i = 0; i < _arity; i++) {
        if (env.signature->isTermAlgebraSort(_type->arg(i))) {
          _indPos[i] = _indPos[i] || (*b._header->nthArgument(i) != *r->nthArgument(i));
        }
      }
    }
  }
  return true;
  // return InductionPreprocessor::checkWellFoundedness(relatedTerms);
}

InductionTemplate::InductionTemplate(const Term* t)
    : _functor(t->functor()), _arity(t->arity()), _isLit(t->isLiteral()),
    _type(_isLit ? env.signature->getPredicate(_functor)->predType()
                 : env.signature->getFunction(_functor)->fnType()),
    _branches(), _indPos(_arity, false) {}

void InductionTemplate::addBranch(vvector<Term*>&& recursiveCalls, Term* header)
{
  CALL("InductionTemplate::addBranch");

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

vstring InductionTemplate::toString() const
{
  vstringstream str;
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

bool checkWellFoundednessHelper(const vvector<pair<Term*,Term*>>& relatedTerms,
  const vset<unsigned>& indices, const vset<unsigned>& positions)
{
  CALL("checkWellFoundednessHelper");

  if (indices.empty()) {
    return true;
  }
  if (positions.empty()) {
    return false;
  }
  for (const auto& p : positions) {
    vset<unsigned> newInd;
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

bool InductionPreprocessor::checkWellFoundedness(const vvector<pair<Term*,Term*>>& relatedTerms)
{
  CALL("static InductionPreprocessor::checkWellFoundedness");

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
  vset<unsigned> positions;
  for (unsigned i = 0; i < arity; i++) {
    if (env.signature->isTermAlgebraSort(type->arg(i))) {
      positions.insert(i);
    }
  }
  vset<unsigned> indices;
  for (unsigned i = 0; i < relatedTerms.size(); i++) {
    indices.insert(i);
  }
  return checkWellFoundednessHelper(relatedTerms, indices, positions);
}

bool InductionPreprocessor::checkWellDefinedness(const vvector<Term*>& cases, vvector<vvector<TermList>>& missingCases)
{
  CALL("InductionPreprocessor::checkWellFoundedness");
  return true;

  // if (cases.empty()) {
  //   return false;
  // }
  // missingCases.clear();
  // auto arity = cases[0]->arity();
  // if (arity == 0) {
  //   return true;
  // }
  // vvector<vvector<TermStack>> availableTermsLists;
  // availableTermsLists.emplace_back(arity);
  // unsigned var = 0;
  // for (unsigned i = 0; i < arity; i++) {
  //   availableTermsLists.back()[i].push(TermList(var++, false));
  // }

  // for (auto& c : cases) {
  //   vvector<vvector<TermStack>> nextAvailableTermsLists;
  //   for (unsigned i = 0; i < arity; i++) {
  //     auto arg = *c->nthArgument(i);
  //     // we check lazily for non-term algebra sort non-variables
  //     if (arg.isTerm() && env.signature->isTermAlgebraSort(SortHelper::getResultSort(arg.term()))) {
  //       auto tempLists = availableTermsLists;
  //       for (auto& availableTerms : tempLists) {
  //         TermAlgebra::excludeTermFromAvailables(availableTerms[i], arg, var);
  //       }
  //       nextAvailableTermsLists.insert(nextAvailableTermsLists.end(),
  //         tempLists.begin(), tempLists.end());
  //     } else {
  //       for (const auto& availableTerms : availableTermsLists) {
  //         if (!availableTerms[i].isEmpty()) {
  //           break;
  //         }
  //       }
  //     }
  //   }
  //   availableTermsLists = nextAvailableTermsLists;
  // }

  // for (const auto& availableTerms : availableTermsLists) {
  //   bool valid = true;
  //   vvector<vvector<TermList>> argTuples(1);
  //   for (const auto& v : availableTerms) {
  //     if (v.isEmpty()) {
  //       valid = false;
  //       break;
  //     }
  //     vvector<vvector<TermList>> temp;
  //     for (const auto& e : v) {
  //       for (auto a : argTuples) {
  //         a.push_back(e);
  //         temp.push_back(a);
  //       }
  //     }
  //     argTuples = temp;
  //   }
  //   if (valid) {
  //     missingCases.insert(missingCases.end(),
  //       argTuples.begin(), argTuples.end());
  //   }
  // }
  // return missingCases.empty();
}

} // Shell
