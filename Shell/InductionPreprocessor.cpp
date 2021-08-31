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

#include "Kernel/Matcher.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Signature.hpp"

using namespace Kernel;

namespace Shell {

bool skolem(Term* t)
{
  ASS(!t->isLiteral());
  return env.signature->getFunction(t->functor())->skolem();
}

bool containsSkolem(Term* t)
{
  CALL("containsSkolem");

  ASS(!t->isLiteral());
  NonVariableIterator nvi(t, true /* includeSelf */);
  while (nvi.hasNext()) {
    auto st = nvi.next();
    if (skolem(st.term())) {
      return true;
    }
  }
  return false;
}

bool canInductOn(Term* t)
{
  CALL("canInductOn");

  static bool complexTermsAllowed = env.options->inductionOnComplexTerms();
  return skolem(t) || (complexTermsAllowed && containsSkolem(t));
}

void FnDefHandler::handleClause(Clause* c, unsigned fi, bool reversed)
{
  CALL("FnDefHandler::handleClause");

  auto lit = (*c)[fi];
  auto trueFun = lit->isEquality();
  Term* header;
  vvector<Term*> recursiveCalls;
  unsigned fn;

  if (trueFun) {
    ASS(lit->isPositive());
    ASS(lit->nthArgument(reversed ? 1 : 0)->isTerm());
    header = lit->nthArgument(reversed ? 1 : 0)->term();
    TermList body = *lit->nthArgument(reversed ? 0 : 1);
    ASS(lit->nthArgument(reversed ? 1 : 0)->containsAllVariablesOf(body));

    static const bool fnrw = env.options->functionDefinitionRewriting();
    if (fnrw) {
      _is->insert(TermList(header), lit, c);
    }

    fn = header->functor();
    InductionPreprocessor::processCase(fn, body, recursiveCalls);
  } else {
    // look for other literals with the same top-level functor
    fn = lit->functor();
    header = lit->isPositive() ? lit : Literal::complementaryLiteral(lit);
    for(unsigned i = 0; i < c->length(); i++) {
      if (fi != i) {
        Literal* curr = (*c)[i];
        if (!curr->isEquality() && fn == curr->functor()) {
          recursiveCalls.push_back(curr->isPositive() ? curr : Literal::complementaryLiteral(curr));
        }
      }
    }
  }
  auto p = make_pair(fn, trueFun);
  auto templIt = _templates.find(p);
  if (templIt == _templates.end()) {
    templIt = _templates.insert(make_pair(p, InductionTemplate(header))).first;
  }

  templIt->second.addBranch(std::move(recursiveCalls), std::move(header));
}

void FnDefHandler::finalize()
{
  CALL("FnDefHandler::finalize");

  for (auto it = _templates.begin(); it != _templates.end();) {
    if (!it->second.finalize()) {
      if (env.options->showInduction()) {
        env.beginOutput();
        env.out() << "% Warning: " << it->second << " discarded" << endl;
        env.endOutput();
      }
      it = _templates.erase(it);
      continue;
    } else {
      if (env.options->showInduction()){
        env.beginOutput();
        if (it->first.second) {
          env.out() << "[Induction] function: " << env.signature->getFunction(it->first.first)->name() << endl;
        } else {
          env.out() << "[Induction] predicate: " << env.signature->getPredicate(it->first.first)->name() << endl;
        }
        env.out() << ", with induction template: " << it->second << endl;
        env.endOutput();
      }
      it++;
    }
  }
}

void FnDefHandler::requestStructuralInductionScheme(Term* t, vvector<InductionScheme>& schemes)
{
  CALL("FnDefHandler::requestStructuralInductionScheme");

  TermAlgebra* ta = env.signature->getTermAlgebraOfSort(env.signature->getFunction(t->functor())->fnType()->result());
  auto it = _taCaseMap.find(ta);
  if (it == _taCaseMap.end()) {
    vvector<InductionScheme::Case> cases;
    unsigned var = 1;
    for (unsigned i = 0; i < ta->nConstructors(); i++) {
      vvector<Substitution> recursiveCalls;

      TermAlgebraConstructor* con = ta->constructor(i);
      unsigned arity = con->arity();
      Stack<TermList> argTerms;
      for (unsigned i = 0; i < arity; i++) {
        TermList v(var++, false);
        if (con->argSort(i) == ta->sort()) {
          recursiveCalls.emplace_back();
          recursiveCalls.back().bind(0, v);
        }
        argTerms.push(v);
      }
      Substitution step;
      step.bind(0, TermList(Term::create(con->functor(),(unsigned)argTerms.size(), argTerms.begin())));
      cases.emplace_back(std::move(recursiveCalls), std::move(step));
    }
    it = _taCaseMap.insert(make_pair(ta, std::move(cases))).first;
  }
  InductionTerms inductionTerms;
  inductionTerms.insert(make_pair(t, 0));
  InductionScheme scheme(inductionTerms, true);
  scheme._cases = &it->second;
  scheme.finalize();
  schemes.push_back(std::move(scheme));
}

bool InductionScheme::finalize()
{
  CALL("InductionScheme::finalize");

  if (_noChecks) {
    _finalized = true;
    return true;
  }
  ALWAYS(addBaseCases());
  _cases->shrink_to_fit();
  vvector<pair<Term*,Term*>> relatedTerms;
  for (auto& c : *_cases) {
    auto mainTerm = InductionScheme::createRepresentingTerm(_inductionTerms, c._step);
    for (auto& recCall : c._recursiveCalls) {
      auto recTerm = InductionScheme::createRepresentingTerm(_inductionTerms, recCall);
      relatedTerms.push_back(make_pair(mainTerm, recTerm));
    }
  }
  _finalized = true;
  return InductionPreprocessor::checkWellFoundedness(relatedTerms);
}

bool InductionScheme::addBaseCases()
{
  CALL("InductionScheme::addBaseCases");

  vvector<Term*> cases;
  vvector<vvector<TermList>> missingCases;
  for (const auto& c : *_cases) {
    cases.push_back(InductionScheme::createRepresentingTerm(_inductionTerms, c._step));
  }
  auto res = InductionPreprocessor::checkWellDefinedness(cases, missingCases);

  for (auto c : missingCases) {
    Substitution step;
    auto it = c.begin();
    for (const auto& kv : _inductionTerms) {
      step.bind(kv.second, *it);
      it++;
    }
    vvector<Substitution> emptyRecCalls;
    _cases->emplace_back(std::move(emptyRecCalls), std::move(step));
  }
  return res;
}

Term* InductionScheme::createRepresentingTerm(const InductionTerms& inductionTerms, const Substitution& s)
{
  CALL("InductionScheme::createRepresentingTerm");

  Stack<TermList> argSorts;
  Stack<TermList> args;
  TermList arg;
  for (const auto& kv : inductionTerms) {
    auto fn = env.signature->getFunction(kv.first->functor())->fnType();
    argSorts.push(fn->result());
    if (s.findBinding(kv.second, arg)) {
      args.push(arg);
    } else {
      args.push(TermList(kv.second, false));
    }
  }
  static DHMap<Stack<TermList>,unsigned> symbols;
  if (!symbols.find(argSorts)) {
    unsigned sym = env.signature->addFreshFunction(argSorts.size(), "indhelper");
    env.signature->getFunction(sym)->setType(
      OperatorType::getFunctionType(argSorts.size(), argSorts.begin(), Term::defaultSort()));
    symbols.insert(argSorts, sym);
  }
  return Term::create(symbols.get(argSorts), args.size(), args.begin());
}

ostream& operator<<(ostream& out, const InductionScheme& scheme)
{
  unsigned k = 0;
  auto indTerms = scheme.inductionTerms();
  auto cases = scheme.cases();
  unsigned l = indTerms.size();
  out << '[';
  for (const auto& kv : indTerms) {
    out << *kv.first << " -> " << kv.second;
    if (++k < l) {
      out << ',';
    }
  }
  out << "]:";
  unsigned j = 0;
  for (const auto& c : cases) {
    unsigned i = 0;
    for (const auto& recCall : c._recursiveCalls) {
      out << recCall;
      if (++i < c._recursiveCalls.size()) {
        out << ',';
      }
    }
    if (!c._recursiveCalls.empty()) {
      out << "=>";
    }
    out << c._step;
    if (++j < cases.size()) {
      out << ';';
    }
  }

  return out;
}

ostream& operator<<(ostream& out, const InductionTemplate::Branch& branch)
{
  if (!branch._recursiveCalls.empty()) {
    out << "(";
    unsigned n = 0;
    for (const auto& r : branch._recursiveCalls) {
      out << *r;
      if (++n < branch._recursiveCalls.size()) {
        out << " & ";
      }
    }
    out << ") => ";
  }
  out << *branch._header;
  return out;
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
      env.out() << "% Warning: adding missing cases to template " << *this;
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
      env.out() << ". New template is " << *this << endl;
      env.endOutput();
    }
  }
}

void InductionTemplate::requestInductionScheme(Term* t, vset<InductionScheme>& schemes)
{
  CALL("InductionTemplate::requestInductionScheme");

  TermStack args;
  vvector<TermList> usedArgs;
  unsigned var = 0;
  InductionTerms inductionTerms;
  // if the induction terms are distinct, no need to check well-foundedness
  // and well-definedness since we already checked it in preprocessing
  for (unsigned i = 0; i < t->arity(); i++) {
    auto arg = *t->nthArgument(i);
    if (_indPos[i]) {
      if (arg.isVar() || !canInductOn(arg.term())) {
        return;
      }
      auto it = inductionTerms.find(arg.term());
      if (it == inductionTerms.end()) {
        it = inductionTerms.insert(make_pair(arg.term(), var++)).first;
      }
      TermList v(it->second, false);
      args.push(v);
      usedArgs.push_back(v);
    // } else if (_usedNonInductionPositions[i]) {
    //   args.push(TermList(var++, false));
    } else {
      args.push(arg);
    }
  }
  if (_invalids.count(usedArgs)) {
    return;
  }
  auto it = _caseMap.find(usedArgs);
  if (it != _caseMap.end()) {
    InductionScheme res(inductionTerms);
    res._cases = &it->second;
    res._finalized = true;
    schemes.insert(std::move(res));
    return;
  }
  vvector<InductionScheme::Case> cases;
  auto isLit = t->isLiteral();
  Term* genTerm;
  if (isLit) {
    genTerm = Literal::create(static_cast<Literal*>(t), args.begin());
  } else {
    genTerm = Term::create(t, args.begin());
  }
  for (auto b : _branches) {
    RobSubstitution subst;
    Renaming r(var);
    if (subst.unify(TermList(b._header), 0, TermList(genTerm), 1)) {
      Term* headerST;
      if (isLit) {
        headerST = subst.apply(static_cast<Literal*>(b._header), 0);
      } else {
        headerST = subst.apply(TermList(b._header), 0).term();
      }
      Substitution mainSubst;
      for (unsigned i = 0; i < t->arity(); i++) {
        if (_indPos[i]) {
          ASS((*genTerm->nthArgument(i)).isVar());
          auto v = (*genTerm->nthArgument(i)).var();
          TermList b;
          auto arg = *headerST->nthArgument(i);
          r.normalizeVariables(arg);
          if (!mainSubst.findBinding(v, b)) {
            mainSubst.bind(v, r.apply(arg));
          } else {
            ASS_EQ(b, r.apply(arg));
          }
        }
      }
      vvector<Substitution> hypSubsts;
      for (auto& recCall : b._recursiveCalls) {
        Term* recCallST;
        if (isLit) {
          recCallST = subst.apply(static_cast<Literal*>(recCall), 0);
        } else {
          recCallST = subst.apply(TermList(recCall), 0).term();
        }
        hypSubsts.emplace_back();
        for (unsigned i = 0; i < t->arity(); i++) {
          if (_indPos[i]) {
            ASS((*genTerm->nthArgument(i)).isVar());
            auto v = (*genTerm->nthArgument(i)).var();
            TermList b;
            auto arg = *recCallST->nthArgument(i);
            r.normalizeVariables(arg);
            if (!hypSubsts.back().findBinding(v, b)) {
              hypSubsts.back().bind(v, r.apply(arg));
            } else if (b != r.apply(arg)) {
              hypSubsts.pop_back();
              break;
            }
          }
        }
      }
      cases.emplace_back(std::move(hypSubsts), std::move(mainSubst));
    }
    var = r.nextVar();
  }
  it = _caseMap.insert(make_pair(std::move(usedArgs), std::move(cases))).first;
  InductionScheme res(inductionTerms);
  res._cases = &it->second;
  if (!res.finalize()) {
    _invalids.insert(usedArgs);
    return;
  }

  if (env.options->showInduction()) {
    env.beginOutput();
    env.out() << "[Induction] induction scheme " << res << " was suggested by "
              << (_isLit ? static_cast<Literal*>(t)->predicateName() : t->functionName()) << endl;
    env.endOutput();
  }
  schemes.insert(std::move(res));
}

bool InductionTemplate::Branch::contains(InductionTemplate::Branch other)
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

bool InductionTemplate::checkUsefulness()
{
  CALL("InductionTemplate::checkUsefulness");

  // discard whenever:
  // (1) no r-descriptions or
  // (2) no terms in any argument positions or
  // (3) no recursive calls
  bool discard = true;
  for (const auto& p : _indPos) {
    if (p) {
      discard = false;
    }
  }
  if (discard) {
    auto t = _branches.begin()->_header;
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

VList* getVariables(TermList t) {
  if (t.isVar()) {
    return VList::singleton(t.var());
  }
  return t.freeVariables();
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
  for (unsigned i = 0; i < _arity; i++) {
    if (!_indPos[i]) {
      for (auto& b : _branches) {
        VList::Iterator vit(getVariables((*b._header)[i]));
        while (vit.hasNext()) {
          auto v = vit.next();
          for (unsigned j = 0; j < _arity; j++) {
            if (i != j/*  && _inductionPositions[j] */) {
              if (VList::member(v, getVariables((*b._header)[j]))) {
                _usedNonIndPos[i] = true;
                break;
              }
              for (auto& r : b._recursiveCalls) {
                if (VList::member(v, getVariables((*r)[j]))) {
                  _usedNonIndPos[i] = true;
                  break;
                }
              }
              if (_usedNonIndPos[i]) {
                break;
              }
            }
          }
          if (_usedNonIndPos[i]) {
            break;
          }
        }
      }
    }
  }
  return InductionPreprocessor::checkWellFoundedness(relatedTerms);
}

InductionTemplate::InductionTemplate(Term* t)
    : _functor(t->functor()), _arity(t->arity()), _isLit(t->isLiteral()),
    _type(_isLit ? env.signature->getPredicate(_functor)->predType()
                 : env.signature->getFunction(_functor)->fnType()),
    _branches(), _indPos(_arity, false), _usedNonIndPos(_arity, false),
    _caseMap(), _invalids() {}

void InductionTemplate::addBranch(vvector<Term*>&& recursiveCalls, Term*&& header)
{
  CALL("InductionTemplate::addBranch");

  ASS(header->arity() == _arity && header->isLiteral() == _isLit && header->functor() == _functor);
  InductionTemplate::Branch branch(recursiveCalls, header);
  for (auto b : _branches) {
    if (b.contains(branch)) {
      return;
    }
  }
  _branches.erase(remove_if(_branches.begin(), _branches.end(),
  [&branch](const InductionTemplate::Branch& b){
    return branch.contains(b);
  }), _branches.end());
  _branches.push_back(std::move(branch));
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
  out << " with positions: (";
  for (unsigned i = 0; i < templ._arity; i++) {
    if (templ._indPos[i]) {
      out << "i";
    } else if (templ._usedNonIndPos[i]) {
      out << "n";
    } else {
      out << "0";
    }
    if (i+1 < templ._arity) {
      out << ",";
    }
  }
  out << ")";
  return out;
}

void InductionPreprocessor::processCase(const unsigned fn, TermList body, vvector<Term*>& recursiveCalls)
{
  CALL("InductionPreprocessor::processCase");

  // If we arrived at a variable, nothing to do
  if (!body.isTerm()) {
    return;
  }

  NonVariableIterator it(body.term(), true);
  while (it.hasNext()) {
    auto st = it.next();
    if (st.term()->functor() == fn) {
      recursiveCalls.push_back(st.term());
    }
  }
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

  if (cases.empty()) {
    return false;
  }
  missingCases.clear();
  auto arity = cases[0]->arity();
  if (arity == 0) {
    return true;
  }
  vvector<vvector<TermStack>> availableTermsLists;
  availableTermsLists.emplace_back(arity);
  unsigned var = 0;
  for (unsigned i = 0; i < arity; i++) {
    availableTermsLists.back()[i].push(TermList(var++, false));
  }

  for (auto& c : cases) {
    vvector<vvector<TermStack>> nextAvailableTermsLists;
    for (unsigned i = 0; i < arity; i++) {
      auto arg = *c->nthArgument(i);
      // we check lazily for non-term algebra sort non-variables
      if (arg.isTerm() && env.signature->isTermAlgebraSort(SortHelper::getResultSort(arg.term()))) {
        auto tempLists = availableTermsLists;
        for (auto& availableTerms : tempLists) {
          TermAlgebra::excludeTermFromAvailables(availableTerms[i], arg, var);
        }
        nextAvailableTermsLists.insert(nextAvailableTermsLists.end(),
          tempLists.begin(), tempLists.end());
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
    vvector<vvector<TermList>> argTuples(1);
    for (const auto& v : availableTerms) {
      if (v.isEmpty()) {
        valid = false;
        break;
      }
      vvector<vvector<TermList>> temp;
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
