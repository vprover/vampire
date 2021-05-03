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

using namespace Kernel;

namespace Shell {

inline bool skolem(TermList t) {
  return !t.isVar() && env.signature->getFunction(t.term()->functor())->skolem();
}

inline bool containsSkolem(TermList t)
{
  if (skolem(t)) {
    return true;
  }
  SubtermIterator stit(t.term());
  while (stit.hasNext()) {
    auto st = stit.next();
    if (env.signature->getFunction(st.term()->functor())->skolem()) {
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
  if (env.signature->hasInductionTemplate(f, false /*pred*/)) {
    auto& templ = env.signature->getInductionTemplate(f, false /*pred*/);
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
      auto st = *t.term()->nthArgument(i);
      if (type->arg(i) == type->result()) {
        auto indTerms = getInductionTerms(st);
        v.insert(v.end(), indTerms.begin(), indTerms.end());
      }
    }
  }
  return v;
}

TermList TermReplacement2::transformSubterm(TermList trm)
{
  auto rIt = _r.find(trm);
  if (rIt != _r.end()) {
    return rIt->second;
  }
  return trm;
}

TermList TermOccurrenceReplacement2::transformSubterm(TermList trm)
{
  auto rIt = _r.find(trm);
  if (rIt != _r.end()) {
    auto oIt = _o.find(make_pair(_lit,trm));
    ASS(oIt != _o.end());
    if (oIt->second.pop_last()) {
      return rIt->second;
    }
  }
  return trm;
}

bool InductionScheme::Case::contains(const InductionScheme::Case& other, unsigned& var) const
{
  RobSubstitution subst;
  vset<TermList> indTerms;
  for (const auto& kv : _step) {
    indTerms.insert(kv.first);
  }
  for (const auto& kv : other._step) {
    indTerms.insert(kv.first);
  }
  auto repr1 = createRepresentingTerm(indTerms, _step, var);
  auto repr2 = createRepresentingTerm(indTerms, other._step, var);
  if (!subst.unify(repr1, 0, repr2, 1)) {
    return false;
  }

  for (const auto& recCall2 : other._recursiveCalls) {
    bool found = false;
    for (const auto& recCall1 : _recursiveCalls) {
      auto repr1rc = createRepresentingTerm(indTerms, recCall1, var);
      auto repr2rc = createRepresentingTerm(indTerms, recCall2, var);
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
  for (const auto& c : _cases) {
    for (const auto& kv : c._step) {
      _inductionTerms.insert(kv.first);
      auto fv = kv.second.freeVariables();
      while (fv != nullptr) {
        _maxVar = max(_maxVar, (unsigned)fv->head());
        fv = fv->tail();
      }
      Formula::VarList::destroy(fv);
    }
    for (const auto& rc : c._recursiveCalls) {
      for (const auto& kv : rc) {
        _inductionTerms.insert(kv.first);
        auto fv = kv.second.freeVariables();
        while (fv != nullptr) {
          _maxVar = max(_maxVar, (unsigned)fv->head());
          fv = fv->tail();
        }
        Formula::VarList::destroy(fv);
      }
    }
  }
  unsigned var = _maxVar;
  for (unsigned i = 0; i < _cases.size(); i++) {
    for (unsigned j = i+1; j < _cases.size();) {
      if (_cases[i].contains(_cases[j], var)) {
        _cases[j] = _cases.back();
        _cases.pop_back();
      } else {
        j++;
      }
    }
  }
  addBaseCases();
  _cases.shrink_to_fit();
  vvector<pair<TermList,TermList>> relatedTerms;
  for (auto& c : _cases) {
    auto mainTerm = InductionScheme::createRepresentingTerm(_inductionTerms, c._step, var);
    for (auto& recCall : c._recursiveCalls) {
      auto recTerm = InductionScheme::createRepresentingTerm(_inductionTerms, recCall, var);
      relatedTerms.push_back(make_pair(mainTerm, recTerm));
    }
  }
  _finalized = true;
  return InductionPreprocessor::checkWellFoundedness(relatedTerms);
}

void InductionScheme::addBaseCases() {
  unsigned var = _maxVar;
  vvector<vmap<TermList, vvector<TermList>>> availableTermsLists(1); // contains one empty map
  for (const auto& c : _cases) {
    vvector<vmap<TermList, vvector<TermList>>> nextAvailableTermsLists;
    for (const auto& kv : c._step) {
      if (kv.second.isTerm()) {
        auto tempLists = availableTermsLists;
        for (auto& availableTerms : tempLists) {
          auto pIt = availableTerms.find(kv.first);
          if (pIt == availableTerms.end()) {
            pIt = availableTerms.insert(
              make_pair(kv.first, TermAlgebra::generateAvailableTerms(kv.first.term(), var))).first;
          }
          TermAlgebra::excludeTermFromAvailables(pIt->second, kv.second, var);
        }
        nextAvailableTermsLists.insert(nextAvailableTermsLists.end(),
          tempLists.begin(), tempLists.end());
      }
    }
    availableTermsLists = nextAvailableTermsLists;
  }

  // We have a set here so there are no duplicate cases
  vset<vmap<TermList, TermList>> steps;
  for (const auto& availableTerms : availableTermsLists) {
    vvector<vmap<TermList, TermList>> temp(1);
    auto invalid = false;
    for (const auto& kv : availableTerms) {
      if (kv.second.empty()) {
        invalid = true;
        break;
      }
      vvector<vmap<TermList, TermList>> newTemp;
      for (const auto& p : kv.second) {
        for (auto step : temp) { // intentionally copy step here
          ASS(!step.count(kv.first));
          step.insert(make_pair(kv.first, p));
          newTemp.push_back(step);
        }
      }
      temp = newTemp;
    }
    if (!invalid) {
      steps.insert(temp.begin(), temp.end());
    }
  }

  // each step gets an empty recursive call and condition set
  var = _maxVar;
  for (auto step : steps) {
    vvector<vmap<TermList,TermList>> emptyRecCalls;
    _cases.emplace_back(std::move(emptyRecCalls), std::move(step));
  }
  _maxVar = var;
}

TermList InductionScheme::createRepresentingTerm(const vset<TermList>& inductionTerms, const vmap<TermList,TermList>& r, unsigned& var)
{
  Stack<unsigned> argSorts;
  Stack<TermList> args;
  for (const auto& indTerm : inductionTerms) {
    auto fn = env.signature->getFunction(indTerm.term()->functor())->fnType();
    argSorts.push(fn->result());
    auto it = r.find(indTerm);
    if (it == r.end()) {
      args.push(TermList(var++, false));
    } else {
      args.push(it->second);
    }
  }
  static DHMap<Stack<unsigned>,unsigned> symbols;
  if (!symbols.find(argSorts)) {
    unsigned sym = env.signature->addFreshFunction(argSorts.size(), "indhelper");
    env.signature->getFunction(sym)->setType(
      OperatorType::getFunctionType(argSorts.size(), argSorts.begin(), 0));
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
  for (const auto& indTerm : indTerms) {
    out << indTerm;
    if (++k < l) {
      out << ',';
    }
  }
  out << ':';
  unsigned j = 0;
  for (const auto& c : cases) {
    unsigned i = 0;
    for (const auto& recCall : c._recursiveCalls) {
      out << '[';
      k = 0;
      for (const auto& indTerm : indTerms) {
        auto it = recCall.find(indTerm);
        out << ((it != recCall.end()) ? it->second.toString() : "_");
        if (++k < l) {
          out << ',';
        }
      }
      out << ']';
      if (++i < c._recursiveCalls.size()) {
        out << ',';
      }
    }
    if (!c._recursiveCalls.empty()) {
      out << "=>";
    }
    k = 0;
    out << '[';
    for (const auto& indTerm : indTerms) {
      auto it = c._step.find(indTerm);
      out << ((it != c._step.end()) ? it->second.toString() : "_");
      if (++k < l) {
        out << ',';
      }
    }
    out << ']';
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

  vvector<InductionScheme> primarySchemes;
  vvector<InductionScheme> secondarySchemes;
  _actOccMaps.clear();

  static vset<Literal*> litsProcessed;
  litsProcessed.clear();
  litsProcessed.insert(main.literal);

  generate(main.clause, main.literal, primarySchemes);
  for (const auto& s : side) {
    if (litsProcessed.insert(s.first).second) {
      generate(s.second, s.first, primarySchemes);
      // generate(s.second, s.first, secondarySchemes);
    }
  }
  for (auto& o : _actOccMaps) {
    o.second.finalize();
  }
  for (unsigned i = 0; i < primarySchemes.size();) {
    auto found = false;
    for (const auto& indTerm : primarySchemes[i].inductionTerms()) {
      auto it = _actOccMaps.find(make_pair(main.literal, indTerm));
      if (it != _actOccMaps.end() && it->second.num_set_bits()) {
        found = true;
        break;
      }
    }
    if (!found) {
      primarySchemes[i] = primarySchemes.back();
      primarySchemes.pop_back();
    } else {
      i++;
    }
  }
  InductionSchemeFilter f;
  f.filter(primarySchemes, secondarySchemes);
  f.filterComplex(primarySchemes, _actOccMaps);

  for (const auto& sch : primarySchemes) {
    OccurrenceMap necessary;
    for (const auto& kv : _actOccMaps) {
      if (sch.inductionTerms().count(kv.first.second)) {
        necessary.insert(kv);
      }
    }
    res.push_back(make_pair(sch, necessary));
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
  vmap<TermList, unsigned> varMap;
  for (unsigned i = 0; i < t->arity(); i++) {
    auto arg = *t->nthArgument(i);
    if (indPos[i]) {
      if (!containsSkolem(arg)) {
        return;
      }
      auto it = varMap.find(arg);
      if (it == varMap.end()) {
        it = varMap.insert(make_pair(arg, var++)).first;
      }
      args.push(TermList(it->second, false));
    } else {
      args.push(arg);
    }
  }
  TermList genTerm;
  auto isLit = t->isLiteral();
  if (isLit) {
    genTerm = TermList(Literal::create(static_cast<Literal*>(t), args.begin()));
  } else {
    genTerm = TermList(Term::create(t, args.begin()));
  }
  InductionScheme res;
  for (auto b : templ.branches()) {
    RobSubstitution subst;
    if (subst.unify(b._header, 0, genTerm, 1)) {
      Term* headerST;
      if (isLit) {
        headerST = subst.apply(static_cast<Literal*>(b._header.term()), 0);
      } else {
        headerST = subst.apply(b._header, 0).term();
      }
      vmap<TermList, TermList> mainSubst;
      for (unsigned i = 0; i < t->arity(); i++) {
        if (indPos[i]) {
          mainSubst.insert(make_pair(*t->nthArgument(i), *headerST->nthArgument(i)));
        }
      }
      vvector<vmap<TermList, TermList>> hypSubsts;
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
            hypSubsts.back().insert(make_pair(*t->nthArgument(i), *recCallST->nthArgument(i)));
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
    auto p = make_pair(lit,curr);
    auto aIt = _actOccMaps.find(p);
    if (aIt == _actOccMaps.end()) {
      _actOccMaps.insert(make_pair(p, Occurrences(active)));
    } else {
      aIt->second.add(active);
    }
  }

  unsigned f = t->functor();
  bool isPred = t->isLiteral();

  // If function with recursive definition, create a scheme
  if (env.signature->hasInductionTemplate(f, isPred)) {
    auto& templ = env.signature->getInductionTemplate(f, isPred);
    const auto& indPos = templ.inductionPositions();

    for (int i = t->arity()-1; i >= 0; i--) {
      actStack.push(indPos[i] && active);
    }

    if (!active) {
      return;
    }

    if (_aggressiveMode) {
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

  static Options::InductionChoice kind = env.options->inductionChoice();
  static bool all = (kind == Options::InductionChoice::ALL);
  static bool goal_plus = (kind == Options::InductionChoice::GOAL_PLUS);
  static bool structInd = env.options->induction() == Options::Induction::BOTH ||
                         env.options->induction() == Options::Induction::STRUCTURAL;
  static bool mathInd = env.options->induction() == Options::Induction::BOTH ||
                         env.options->induction() == Options::Induction::MATHEMATICAL;
  static bool complexTermsAllowed = env.options->inductionOnComplexTerms();

  Set<Term*> ta_terms;
  Set<Term*> int_terms;
  SubtermIterator it(main.literal);
  while(it.hasNext()){
    TermList ts = it.next();
    ASS(ts.isTerm());
    unsigned f = ts.term()->functor();
    if((complexTermsAllowed || env.signature->functionArity(f)==0) &&
        (
            all
        || env.signature->getFunction(f)->inGoal()
        || (goal_plus && env.signature->getFunction(f)->inductionSkolem()) // set in NewCNF
        )
    ){
      if(structInd &&
        env.signature->isTermAlgebraSort(env.signature->getFunction(f)->fnType()->result()) &&
        ((complexTermsAllowed && env.signature->functionArity(f) != 0) || !env.signature->getFunction(f)->termAlgebraCons()) // skip base constructors
        ){
        ta_terms.insert(ts.term());
      }
      if(mathInd &&
          env.signature->getFunction(f)->fnType()->result()==Sorts::SRT_INTEGER &&
          !theory->isInterpretedConstant(f)
        ){
        int_terms.insert(ts.term());
      }
    }
    auto p = make_pair(main.literal, ts);
    auto oIt = occMap.find(p);
    if (oIt == occMap.end()) {
      occMap.insert(make_pair(p, Occurrences(false)));
    } else {
      oIt->second.add(false);
    }
  }

  Set<Term*>::Iterator taIt(ta_terms);
  while (taIt.hasNext()) {
    schemes.push_back(generateStructural(taIt.next()));
  }

  for (const auto& qr : side) {
    SubtermIterator it(qr.first);
    while(it.hasNext()){
      TermList ts = it.next();
      auto p = make_pair(qr.first, ts);
      auto oIt = occMap.find(p);
      if (oIt == occMap.end()) {
        occMap.insert(make_pair(p, Occurrences(false)));
      } else {
        oIt->second.add(false);
      }
    }
  }

  for (auto& o : occMap) {
    o.second.finalize();
  }

  for (const auto& sch : schemes) {
    OccurrenceMap necessary;
    for (const auto& kv : occMap) {
      if (sch.inductionTerms().count(kv.first.second)) {
        necessary.insert(kv);
      }
    }
    res.push_back(make_pair(sch, necessary));
  }
}

InductionScheme StructuralInductionSchemeGenerator::generateStructural(Term* term)
{
  CALL("StructuralInductionSchemeGenerator::generateStructural");

  TermAlgebra* ta = env.signature->getTermAlgebraOfSort(env.signature->getFunction(term->functor())->fnType()->result());
  unsigned ta_sort = ta->sort();
  unsigned var = 0;
  InductionScheme scheme;

  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    TermAlgebraConstructor* con = ta->constructor(i);
    vvector<vmap<TermList,TermList>> recursiveCalls;
    vmap<TermList,TermList> step;

    unsigned arity = con->arity();
    Stack<TermList> ta_vars;
    Stack<TermList> argTerms;
    for (unsigned i = 0; i < arity; i++) {
      TermList x(var++,false);
      argTerms.push(x);
      if(con->argSort(i) == ta_sort){
        ta_vars.push(x);
      }
    }
    Stack<TermList>::Iterator tvit(ta_vars);
    while (tvit.hasNext()) {
      vmap<TermList, TermList> recCall;
      recCall.insert(make_pair(term,tvit.next()));
      recursiveCalls.push_back(recCall);
    }
    step.insert(make_pair(term,
      TermList(Term::create(con->functor(),(unsigned)argTerms.size(), argTerms.begin()))));
    scheme.addCase(std::move(recursiveCalls), std::move(step));
  }
  scheme.finalize();
  return scheme;
}

} // Shell
