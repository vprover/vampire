/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "InductionSchemeGenerator.hpp"

#include "Lib/Set.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "InductionSchemeFilter.hpp"

#include "Inferences/InductionHelper.hpp"

using namespace Kernel;

namespace Shell {

inline bool isTermAlgebraCons(Term* t)
{
  ASS(!t->isLiteral());
  return env.signature->getFunction(t->functor())->termAlgebraCons();
}

inline bool skolem(Term* t)
{
  ASS(!t->isLiteral());
  return env.signature->getFunction(t->functor())->skolem();
}

inline bool containsSkolem(Term* t)
{
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

inline bool canInductOn(Term* t)
{
  CALL("canInductOn");

  static bool complexTermsAllowed = env.options->inductionOnComplexTerms();
  return skolem(t) || (complexTermsAllowed && containsSkolem(t));
}

/**
 * Returns all subterms which can be inducted on for a term.
 */
vvector<Term*> getInductionTerms(Term* t)
{
  CALL("getInductionTerms");
  // no predicates here
  ASS(!t->isLiteral());

  vvector<Term*> v;
  if (canInductOn(t)) {
    v.push_back(t);
  }
  unsigned f = t->functor();
  auto type = env.signature->getFunction(f)->fnType();

  // If function with recursive definition,
  // recurse in its active arguments
  if (env.signature->getFnDefHandler()->hasInductionTemplate(f, true /*trueFun*/)) {
    auto& templ = env.signature->getFnDefHandler()->getInductionTemplate(f, true /*trueFun*/);
    const auto& indVars = templ.inductionPositions();

    Term::Iterator argIt(t);
    unsigned i = 0;
    while (argIt.hasNext()) {
      auto arg = argIt.next();
      if (indVars.at(i) && type->arg(i) == type->result() && arg.isTerm()) {
        auto indTerms = getInductionTerms(arg.term());
        v.insert(v.end(), indTerms.begin(), indTerms.end());
      }
      i++;
    }
  } else if (isTermAlgebraCons(t)) {
    for (unsigned i = 0; i < t->arity(); i++) {
      if (type->arg(i) == type->result()) {
        auto st = *t->nthArgument(i);
        if (st.isTerm()) {
          auto indTerms = getInductionTerms(st.term());
          v.insert(v.end(), indTerms.begin(), indTerms.end());
        }
      }
    }
  }
  return v;
}

bool InductionScheme::Case::contains(const InductionScheme::Case& other,
  const vmap<Term*, unsigned>& indTerms1, const vmap<Term*, unsigned>& indTerms2) const
{
  CALL("InductionScheme::Case::contains");

  RobSubstitution subst;
  auto repr1 = createRepresentingTerm(indTerms1, _step);
  auto repr2 = createRepresentingTerm(indTerms2, other._step);
  if (!subst.unify(repr1, 0, repr2, 1)) {
    return false;
  }

  for (const auto& recCall2 : other._recursiveCalls) {
    bool found = false;
    for (const auto& recCall1 : _recursiveCalls) {
      auto repr1rc = createRepresentingTerm(indTerms1, recCall1);
      auto repr2rc = createRepresentingTerm(indTerms2, recCall2);
      repr1rc = subst.apply(repr1rc, 0);
      repr2rc = subst.apply(repr2rc, 1);
      if (repr1rc == repr2rc) {
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

bool InductionScheme::finalize()
{
  CALL("InductionScheme::finalize");

  if (_noChecks) {
    _finalized = true;
    return true;
  }
  // for (unsigned i = 0; i < _cases.size(); i++) {
  //   for (unsigned j = i+1; j < _cases.size();) {
  //     if (_cases[i].contains(_cases[j], _inductionTerms, _inductionTerms)) {
  //       _cases[j] = std::move(_cases[_cases.size()-1]);
  //       _cases.pop_back();
  //     } else {
  //       j++;
  //     }
  //   }
  // }
  ALWAYS(addBaseCases());
  _cases.shrink_to_fit();
  vvector<pair<TermList,TermList>> relatedTerms;
  for (auto& c : _cases) {
    auto mainTerm = InductionScheme::createRepresentingTerm(_inductionTerms, c._step);
    for (auto& recCall : c._recursiveCalls) {
      auto recTerm = InductionScheme::createRepresentingTerm(_inductionTerms, recCall);
      relatedTerms.push_back(make_pair(mainTerm, recTerm));
    }
  }
  _finalized = true;
  return InductionPreprocessor::checkWellFoundedness(relatedTerms);
}

bool InductionScheme::addBaseCases() {
  vvector<Term*> cases;
  vvector<vvector<TermList>> missingCases;
  for (const auto& c : _cases) {
    cases.push_back(InductionScheme::createRepresentingTerm(_inductionTerms, c._step).term());
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
    _cases.emplace_back(std::move(emptyRecCalls), std::move(step));
  }
  return res;
}

TermList InductionScheme::createRepresentingTerm(const vmap<Term*, unsigned>& inductionTerms, const Substitution& s)
{
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

  return TermList(Term::create(symbols.get(argSorts), args.size(), args.begin()));
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

void RecursionInductionSchemeGenerator::generate(
  const SLQueryResult& main,
  const vset<pair<Literal*,Clause*>>& side,
  vvector<pair<InductionScheme, OccurrenceMap>>& res)
{
  CALL("RecursionInductionSchemeGenerator::generate()");

  _schemes.clear();
  _actOccMaps._m.clear();

  static vset<Literal*> litsProcessed;
  litsProcessed.clear();
  litsProcessed.insert(main.literal);

  generate(main.clause, main.literal);
  for (const auto& s : side) {
    if (litsProcessed.insert(s.first).second) {
      generate(s.second, s.first);
    }
  }
  _actOccMaps.finalize();
  // filter out schemes that only contain induction
  // terms not present in the main literal
  _schemes.erase(remove_if(_schemes.begin(), _schemes.end(), [this, &main](const InductionScheme& sch) {
    for (const auto& kv : sch.inductionTerms()) {
      auto it = _actOccMaps._m.find(make_pair(main.literal, kv.first));
      if (it != _actOccMaps._m.end() && it->second.num_set_bits()) {
        return false;
      }
    }
    return true;
  }), _schemes.end());

  static InductionSchemeFilter f;
  f.filter(_schemes, _actOccMaps);

  for (const auto& sch : _schemes) {
    res.push_back(make_pair(sch, _actOccMaps.create_necessary(sch)));
  }
}

void RecursionInductionSchemeGenerator::generate(Clause* premise, Literal* lit)
{
  CALL("RecursionInductionSchemeGenerator::generate");

  // Process all subterms of the literal to
  // be able to store occurrences of induction
  // terms. The literal itself and both sides
  // of the equality count as active positions.

  if (env.options->showInduction()) {
    env.beginOutput();
    env.out() << "[Induction] processing literal " << *lit << endl;
    env.endOutput();
  }

  Stack<bool> actStack;
  process(lit, actStack);
  SubtermIterator it(lit);
  while (it.hasNext()){
    TermList curr = it.next();
    bool active = actStack.pop();
    if (curr.isTerm()) {
      process(curr.term(), active, actStack, lit);
    }
  }
  ASS(actStack.isEmpty());
}

void RecursionInductionSchemeGenerator::addScheme(Term* t, const InductionTemplate& templ)
{
  CALL("RecursionInductionSchemeGenerator::addScheme");

  const auto& indPos = templ.inductionPositions();
  TermStack args;
  unsigned var = 0;
  vmap<Term*, unsigned> inductionTerms;
  // if the induction terms are distinct, no need to check well-foundedness
  // and well-definedness since we already checked it in preprocessing
  bool noChecks = true;
  for (unsigned i = 0; i < t->arity(); i++) {
    auto arg = *t->nthArgument(i);
    if (indPos[i]) {
      if (arg.isVar() || !containsSkolem(arg.term())) {
        return;
      }
      auto it = inductionTerms.find(arg.term());
      if (it == inductionTerms.end()) {
        it = inductionTerms.insert(make_pair(arg.term(), var++)).first;
      } else {
        noChecks = false;
      }
      args.push(TermList(it->second, false));
    } else {
      args.push(arg);
    }
  }
  Term* genTerm;
  auto isLit = t->isLiteral();
  if (isLit) {
    genTerm = Literal::create(static_cast<Literal*>(t), args.begin());
  } else {
    genTerm = Term::create(t, args.begin());
  }
  InductionScheme res(inductionTerms, noChecks);
  for (auto b : templ.branches()) {
    RobSubstitution subst;
    if (subst.unify(b._header, 0, TermList(genTerm), 1)) {
      Term* headerST;
      if (isLit) {
        headerST = subst.apply(static_cast<Literal*>(b._header.term()), 0);
      } else {
        headerST = subst.apply(b._header, 0).term();
      }
      Substitution mainSubst;
      for (unsigned i = 0; i < t->arity(); i++) {
        if (indPos[i]) {
          ASS((*genTerm->nthArgument(i)).isVar());
          auto v = (*genTerm->nthArgument(i)).var();
          TermList b;
          if (!mainSubst.findBinding(v, b)) {
            mainSubst.bind(v, *headerST->nthArgument(i));
          } else {
            ASS_EQ(b, *headerST->nthArgument(i));
          }
        }
      }
      vvector<Substitution> hypSubsts;
      for (auto& recCall : b._recursiveCalls) {
        Term* recCallST;
        if (isLit) {
          recCallST = subst.apply(static_cast<Literal*>(recCall.term()), 0);
        } else {
          recCallST = subst.apply(recCall, 0).term();
        }
        hypSubsts.emplace_back();
        for (unsigned i = 0; i < t->arity(); i++) {
          if (indPos[i]) {
            ASS((*genTerm->nthArgument(i)).isVar());
            auto v = (*genTerm->nthArgument(i)).var();
            TermList b;
            if (!hypSubsts.back().findBinding(v, b)) {
              hypSubsts.back().bind(v, *recCallST->nthArgument(i));
            } else if (b != *recCallST->nthArgument(i)) {
              hypSubsts.pop_back();
              break;
            }
          }
        }
      }
      res.addCase(std::move(hypSubsts), std::move(mainSubst));
    }
  }
  if (!res.finalize()) {
    return;
  }

  if (env.options->showInduction()) {
    env.beginOutput();
    env.out() << "[Induction] induction scheme " << res
              << " was suggested by term " << *t << endl;
    env.endOutput();
  }
  _schemes.push_back(std::move(res));
}

void RecursionInductionSchemeGenerator::handleActiveTerm(Term* t, const InductionTemplate& templ, Stack<bool>& actStack)
{
  const auto& indPos = templ.inductionPositions();

  for (int i = t->arity()-1; i >= 0; i--) {
    actStack.push(indPos[i]);
  }

  static bool exhaustive = env.options->inductionExhaustiveGeneration();
  if (exhaustive) {
    Term::Iterator argIt(t);
    unsigned i = 0;
    vvector<TermStack> argTermsList(1); // initially 1 empty vector
    while (argIt.hasNext()) {
      auto arg = argIt.next();
      if (!indPos[i] || arg.isVar()) {
        for (auto& argTerms : argTermsList) {
          argTerms.push(arg);
        }
      } else {
        auto its = getInductionTerms(arg.term());
        vvector<TermStack> newArgTermsList;
        for (const auto& indTerm : its) {
          for (auto argTerms : argTermsList) {
            argTerms.push(TermList(indTerm));
            newArgTermsList.push_back(std::move(argTerms));
          }
        }
        argTermsList = newArgTermsList;
      }
      i++;
    }

    auto isLit = t->isLiteral();
    for (const auto& argTerms : argTermsList) {
      Term* nt;
      if (isLit) {
        nt = Literal::create(static_cast<Literal*>(t), argTerms.begin());
      } else {
        nt = Term::create(t, argTerms.begin());
      }
      addScheme(nt, templ);
    }
  } else {
    addScheme(t, templ);
  }
}

void RecursionInductionSchemeGenerator::process(Term* t, bool active,
  Stack<bool>& actStack, Literal* lit)
{
  CALL("RecursionInductionSchemeGenerator::process");

  // If induction term, store the occurrence
  if (canInductOn(t)) {
    _actOccMaps.add(lit, t, active);
  }

  unsigned f = t->functor();

  // If function with recursive definition, create a scheme
  if (active && env.signature->getFnDefHandler()->hasInductionTemplate(f, true)) {
    handleActiveTerm(t, env.signature->getFnDefHandler()->getInductionTemplate(f, true), actStack);
  } else {
    for (unsigned i = 0; i < t->arity(); i++) {
      actStack.push(active);
    }
  }
}

void RecursionInductionSchemeGenerator::process(Literal* lit, Stack<bool>& actStack)
{
  CALL("RecursionInductionSchemeGenerator::process");

  unsigned f = lit->functor();

  // If function with recursive definition, create a scheme
  if (env.signature->getFnDefHandler()->hasInductionTemplate(f, false)) {
    handleActiveTerm(lit, env.signature->getFnDefHandler()->getInductionTemplate(f, false), actStack);
  } else {
    for (unsigned i = 0; i < lit->arity(); i++) {
      actStack.push(true);
    }
  }
}

void StructuralInductionSchemeGenerator::generate(
  const SLQueryResult& main,
  const vset<pair<Literal*,Clause*>>& side,
  vvector<pair<InductionScheme, OccurrenceMap>>& res)
{
  CALL("StructuralInductionSchemeGenerator()");

  vvector<InductionScheme> schemes;
  OccurrenceMap occMap;

  Set<Term*> ta_terms;
  SubtermIterator it(main.literal);
  while (it.hasNext()) {
    TermList ts = it.next();
    ASS(ts.isTerm());
    Term* t = ts.term();
    unsigned f = t->functor();
    if (Inferences::InductionHelper::isInductionTermFunctor(f) &&
        Inferences::InductionHelper::isStructInductionFunctor(f)) {
      ta_terms.insert(t);
    }
    occMap.add(main.literal, t, false);
  }

  Set<Term*>::Iterator taIt(ta_terms);
  while (taIt.hasNext()) {
    schemes.push_back(generateStructural(taIt.next()));
  }

  for (const auto& qr : side) {
    SubtermIterator it(qr.first);
    while (it.hasNext()) {
      Term* t = it.next().term();
      occMap.add(qr.first, t, false);
    }
  }

  occMap.finalize();
  for (const auto& sch : schemes) {
    res.push_back(make_pair(sch, occMap.create_necessary(sch)));
  }
}

vvector<pair<Term*, vvector<unsigned>>> generateCases(TermAlgebra* ta)
{
  vvector<pair<Term*, vvector<unsigned>>> res;
  unsigned var = 0;
  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    TermAlgebraConstructor* con = ta->constructor(i);
    unsigned arity = con->arity();
    vvector<unsigned> ta_vars;
    Stack<TermList> argTerms;
    for (unsigned i = 0; i < arity; i++) {
      if (con->argSort(i) == ta->sort()) {
        ta_vars.push_back(var);
      }
      argTerms.push(TermList(var++, false));
    }
    res.push_back(make_pair(Term::create(con->functor(),(unsigned)argTerms.size(), argTerms.begin()), ta_vars));
  }
  return res;
}

InductionScheme StructuralInductionSchemeGenerator::generateStructural(Term* term)
{
  CALL("StructuralInductionSchemeGenerator::generateStructural");

  TermAlgebra* ta = env.signature->getTermAlgebraOfSort(env.signature->getFunction(term->functor())->fnType()->result());
  vmap<Term*, unsigned> inductionTerms;
  inductionTerms.insert(make_pair(term, 0));
  InductionScheme scheme(inductionTerms, true);
  static DHMap<TermAlgebra*, vvector<pair<Term*, vvector<unsigned>>>> taCasesMap;
  vvector<pair<Term*, vvector<unsigned>>> taCases;
  if (!taCasesMap.find(ta, taCases)) {
    taCases = generateCases(ta);
    taCasesMap.insert(ta, taCases);
  }
  for (const auto& kv : taCases) {
    vvector<Substitution> recursiveCalls;
    for (const auto& v : kv.second) {
      recursiveCalls.emplace_back();
      recursiveCalls.back().bind(0,TermList(v, false));
    }
    Substitution step;
    step.bind(0, TermList(kv.first));
    scheme.addCase(std::move(recursiveCalls), std::move(step));
  }
  scheme.finalize();
  return scheme;
}

} // Shell
