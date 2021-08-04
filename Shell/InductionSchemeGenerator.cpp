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
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaVarIterator.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "InductionSchemeFilter.hpp"

#include "Inferences/InductionHelper.hpp"

using namespace Kernel;

namespace Shell {

inline bool skolem(TermList t) {
  if (t.isVar()) {
    return false;
  }
  auto isLit = t.term()->isLiteral();
  auto symb = isLit ? env.signature->getPredicate(t.term()->functor()) : env.signature->getFunction(t.term()->functor());
  return symb->skolem();
}

inline bool containsSkolem(TermList t)
{
  if (skolem(t)) {
    return true;
  }
  SubtermIterator stit(t.term());
  while (stit.hasNext()) {
    auto st = stit.next();
    if (skolem(st)) {
      return true;
    }
  }
  return false;
}

inline bool canInductOn(TermList t)
{
  CALL("canInductOn");

  static bool complexTermsAllowed = env.options->inductionOnComplexTerms();
  return skolem(t) || (complexTermsAllowed && containsSkolem(t));
}

/**
 * Returns all subterms which can be inducted on for a term.
 */
vvector<TermList> getInductionTerms(TermList t)
{
  CALL("getInductionTerms");
  // no predicates or variables here
  ASS(t.isTerm() && !t.term()->isLiteral());

  vvector<TermList> v;
  if (canInductOn(t)) {
    v.push_back(t);
  }
  unsigned f = t.term()->functor();
  auto type = env.signature->getFunction(f)->fnType();

  // If function with recursive definition,
  // recurse in its active arguments
  if (env.signature->getFnDefHandler()->hasInductionTemplate(f, true /*trueFun*/)) {
    auto& templ = env.signature->getFnDefHandler()->getInductionTemplate(f, true /*trueFun*/);
    const auto& indVars = templ.inductionPositions();

    Term::Iterator argIt(t.term());
    unsigned i = 0;
    while (argIt.hasNext()) {
      auto arg = argIt.next();
      if (indVars.at(i) && type->arg(i) == type->result()) {
        auto indTerms = getInductionTerms(arg);
        v.insert(v.end(), indTerms.begin(), indTerms.end());
      }
      i++;
    }
  } else if (isTermAlgebraCons(t)) {
    for (unsigned i = 0; i < t.term()->arity(); i++) {
      if (type->arg(i) == type->result()) {
        auto st = *t.term()->nthArgument(i);
        auto indTerms = getInductionTerms(st);
        v.insert(v.end(), indTerms.begin(), indTerms.end());
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

  vvector<InductionScheme> schemes;
  _actOccMaps._m.clear();

  static vset<Literal*> litsProcessed;
  litsProcessed.clear();
  litsProcessed.insert(main.literal);

  generate(main.clause, main.literal, schemes);
  for (const auto& s : side) {
    if (litsProcessed.insert(s.first).second) {
      generate(s.second, s.first, schemes);
    }
  }
  _actOccMaps.finalize();
  // filter out schemes that only contain induction
  // terms not present in the main literal
  schemes.erase(remove_if(schemes.begin(), schemes.end(), [this, &main](const InductionScheme& sch) {
    for (const auto& kv : sch.inductionTerms()) {
      auto it = _actOccMaps._m.find(make_pair(main.literal, kv.first));
      if (it != _actOccMaps._m.end() && it->second.num_set_bits()) {
        return false;
      }
    }
    return true;
  }), schemes.end());

  static InductionSchemeFilter f;
  f.filter(schemes, _actOccMaps);

  for (const auto& sch : schemes) {
    res.push_back(make_pair(sch, _actOccMaps.create_necessary(sch)));
  }
}

void RecursionInductionSchemeGenerator::generate(Clause* premise, Literal* lit,
  vvector<InductionScheme>& schemes)
{
  CALL("RecursionInductionSchemeGenerator::generate");

  // Process all subterms of the literal to
  // be able to store occurrences of induction
  // terms. The literal itself and both sides
  // of the equality count as active positions.

  Stack<bool> actStack;
  if (lit->isEquality()) {
    actStack.push(true);
    actStack.push(true);
  } else {
    process(TermList(lit), true, actStack, premise, lit, schemes);
  }
  SubtermIterator it(lit);
  while(it.hasNext()){
    TermList curr = it.next();
    bool active = actStack.pop();
    process(curr, active, actStack, premise, lit, schemes);
  }
  ASS(actStack.isEmpty());
}

void RecursionInductionSchemeGenerator::addScheme(Literal* lit, Term* t, const InductionTemplate& templ,
  vvector<InductionScheme>& schemes)
{
  CALL("RecursionInductionSchemeGenerator::addScheme");

  const auto& indPos = templ.inductionPositions();
  TermStack args;
  unsigned var = 0;
  vmap<Term*, unsigned> inductionTerms;
  for (unsigned i = 0; i < t->arity(); i++) {
    auto arg = *t->nthArgument(i);
    if (indPos[i]) {
      if (!containsSkolem(arg)) {
        return;
      }
      auto it = inductionTerms.find(arg.term());
      if (it == inductionTerms.end()) {
        it = inductionTerms.insert(make_pair(arg.term(), var++)).first;
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
  InductionScheme res(inductionTerms);
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
              << " was suggested by term " << *t << " in " << *lit << endl;
    env.endOutput();
  }
  schemes.push_back(std::move(res));
}

void RecursionInductionSchemeGenerator::process(TermList curr, bool active,
  Stack<bool>& actStack, Clause* premise, Literal* lit,
  vvector<InductionScheme>& schemes)
{
  CALL("RecursionInductionSchemeGenerator::process");

  if (!curr.isTerm()) {
    return;
  }
  auto t = curr.term();

  // If induction term, store the occurrence
  if (canInductOn(curr)) {
    _actOccMaps.add(lit, t, active);
  }

  unsigned f = t->functor();
  bool trueFun = !t->isLiteral();

  // If function with recursive definition, create a scheme
  if (env.signature->getFnDefHandler()->hasInductionTemplate(f, trueFun)) {
    auto& templ = env.signature->getFnDefHandler()->getInductionTemplate(f, trueFun);
    const auto& indPos = templ.inductionPositions();

    for (int i = t->arity()-1; i >= 0; i--) {
      actStack.push(indPos[i] && active);
    }

    if (!active) {
      return;
    }

    static bool exhaustive = env.options->inductionExhaustiveGeneration();
    if (exhaustive) {
      Term::Iterator argIt(t);
      unsigned i = 0;
      vvector<TermStack> argTermsList(1); // initially 1 empty vector
      while (argIt.hasNext()) {
        auto arg = argIt.next();
        if (!indPos[i]) {
          for (auto& argTerms : argTermsList) {
            argTerms.push(arg);
          }
        } else {
          auto its = getInductionTerms(arg);
          vvector<TermStack> newArgTermsList;
          for (const auto& indTerm : its) {
            for (auto argTerms : argTermsList) {
              argTerms.push(indTerm);
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
        addScheme(lit, nt, templ, schemes);
      }
    } else {
      addScheme(lit, t, templ, schemes);
    }
  } else {
    for (unsigned i = 0; i < t->arity(); i++) {
      actStack.push(active);
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

InductionScheme StructuralInductionSchemeGenerator::generateStructural(Term* term)
{
  CALL("StructuralInductionSchemeGenerator::generateStructural");

  TermAlgebra* ta = env.signature->getTermAlgebraOfSort(env.signature->getFunction(term->functor())->fnType()->result());
  TermList ta_sort = ta->sort();
  unsigned var = 1;
  vmap<Term*, unsigned> inductionTerms;
  inductionTerms.insert(make_pair(term, 0));
  InductionScheme scheme(inductionTerms, true);

  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    TermAlgebraConstructor* con = ta->constructor(i);
    vvector<Substitution> recursiveCalls;
    Substitution step;

    unsigned arity = con->arity();
    Stack<TermList> ta_vars;
    Stack<TermList> argTerms;
    for (unsigned i = 0; i < arity; i++) {
      TermList x(var++, false);
      argTerms.push(x);
      if (con->argSort(i) == ta_sort) {
        ta_vars.push(x);
      }
    }
    Stack<TermList>::Iterator tvit(ta_vars);
    while (tvit.hasNext()) {
      recursiveCalls.emplace_back();
      recursiveCalls.back().bind(0,tvit.next());
    }
    step.bind(0, TermList(Term::create(con->functor(),(unsigned)argTerms.size(), argTerms.begin())));
    scheme.addCase(std::move(recursiveCalls), std::move(step));
  }
  scheme.finalize();
  return scheme;
}

} // Shell
