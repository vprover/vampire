/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file NewCNF.cpp
 * Implements class NewCNF implementing the new CNF transformation.
 * @since 19/11/2015 Manchester
 */

#include "Debug/Tracer.hpp"

#include "Kernel/OperatorType.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/FormulaVarIterator.hpp"
#include "Shell/Flattening.hpp"
#include "Shell/NameReuse.hpp"
#include "Shell/Skolem.hpp"
#include "Shell/Options.hpp"
#include "Shell/Rectify.hpp"
#include "Shell/SymbolOccurrenceReplacement.hpp"
#include "Shell/SymbolDefinitionInlining.hpp"
#include "Shell/Statistics.hpp"

#include "NewCNF.hpp"

using namespace Lib;
using namespace Kernel;

namespace Shell {

void NewCNF::clausify(FormulaUnit* unit,Stack<Clause*>& output)
{
  CALL("NewCNF::clausify");

  _beingClausified = unit;

  Formula* f = unit->formula();

#if LOGGING
  cout << endl << "----------------- INPUT ------------------" << endl;
  cout << f->toString() << endl;
  cout << "----------------- INPUT ------------------" << endl;
#endif

  switch (f->connective()) {
    case TRUE:
      return;

    case FALSE: {
      // create an empty clause and push it in the stack
      Clause* clause = new(0) Clause(0,FormulaTransformation(InferenceRule::CLAUSIFY,unit));
      output.push(clause);
      return;
    }

    default:
      break;
  }

  ASS(_genClauses.empty());
  ASS(_queue.isEmpty());
  ASS(_occurrences.isEmpty());

  enqueue(f);

  introduceGenClause(GenLit(f, POSITIVE));

  // process the generalized clauses until they contain only literals
  while(_queue.isNonEmpty()) {
    Formula* g;
    Occurrences occurrences;
    dequeue(g, occurrences);

#if LOGGING
    cout << endl << "---------------------------------------------" << endl;
    for (SPGenClause gc : _genClauses) {
      LOG1(gc->toString());
    }
    cout << "---------------------------------------------" << endl << endl;
#endif

    if ((_namingThreshold > 1) && occurrences.size() > _namingThreshold) {
      nameSubformula(g, occurrences);
    } else {
      // TODO: currently we don't check for tautologies, as there should be none appearing (we use polarity based expansion of IFF and XOR)
      process(g, occurrences);
    }
  }

#if LOGGING
  cout << endl << "----------------- OUTPUT -----------------" << endl;
  for (SPGenClause gc : _genClauses) {
    LOG1(gc->toString());
  }
  cout << "----------------- OUTPUT -----------------" << endl;
#endif

  for (SPGenClause gc : _genClauses) {
    toClauses(gc, output);
  }

  _genClauses.clear();
  _varSorts.reset();
  _collectedVarSorts = false;
  _maxVar = 0;
  _freeVars.reset();

  { // destroy the cached substitution entries
    DHMap<BindingList*,Substitution*>::DelIterator dIt(_substitutionsByBindings);
    while (dIt.hasNext()) {
      delete dIt.next();
      dIt.del();
    }
  }

  ASS(_queue.isEmpty());
  ASS(_occurrences.isEmpty());
}

void NewCNF::process(Literal* literal, Occurrences &occurrences) {
  CALL("NewCNF::process(Literal*)");

  LOG2("process(Literal*)", literal->toString());
  LOG2("occurrences.size", occurrences.size());

  // shared literals don't contain fool stuff
  if (literal->shared()) {
    return;
  }

  Stack<unsigned> variables;
  Stack<Formula*> conditions;
  Stack<TermList> thenBranches;
  Stack<TermList> elseBranches;

  Stack<unsigned> matchVariables;
  Stack<List<Formula*>*> matchConditions;
  Stack<List<TermList>*> matchBranches;

  Stack<TermList> arguments;
  Term::Iterator ait(literal);
  while (ait.hasNext()) {
    arguments.push(findITEs(ait.next(), variables, conditions, thenBranches,
      elseBranches, matchVariables, matchConditions, matchBranches));
  }
  Literal* processedLiteral = Literal::create(literal, arguments.begin());

  List<LPair>* literals(0);
  List<LPair>::push(make_pair(processedLiteral, List<GenLit>::empty()),
                    literals);

  LOG4("Found", variables.size(), "variable(s) for ITEs inside", literal->toString());
  LOG3("Replacing it by", processedLiteral->toString(), "with variable substitutions");

  unsigned iteCounter = 0;
  while (variables.isNonEmpty()) {
    unsigned variable   = variables.pop();
    Formula* condition  = conditions.pop();
    TermList thenBranch = thenBranches.pop();
    TermList elseBranch = elseBranches.pop();

    enqueue(condition);

    GenLit positiveCondition = GenLit(condition, POSITIVE);
    GenLit negativeCondition = GenLit(condition, NEGATIVE);

    Substitution thenSubst;
    thenSubst.bind(variable, thenBranch);

    Substitution elseSubst;
    elseSubst.bind(variable, elseBranch);

    List<LPair>* processedLiterals(0);

    if (shouldInlineITE(iteCounter)) {
      while (List<LPair>::isNonEmpty(literals)) {
        LPair p = List<LPair>::pop(literals);
        Literal* literal = p.first;
        List<GenLit>* gls = p.second;

        Literal* thenLiteral = SubstHelper::apply(literal, thenSubst);
        Literal* elseLiteral = SubstHelper::apply(literal, elseSubst);

        LPair thenPair = make_pair(thenLiteral, List<GenLit>::cons(negativeCondition, gls));
        LPair elsePair = make_pair(elseLiteral, List<GenLit>::cons(positiveCondition, gls));

        List<LPair>::push(thenPair, processedLiterals);
        List<LPair>::push(elsePair, processedLiterals);
      }
    } else {
      VarSet* fv = freeVars(condition);
      fv = fv->getUnion(VarSet::getFromIterator(FormulaVarIterator(&thenBranch)));
      fv = fv->getUnion(VarSet::getFromIterator(FormulaVarIterator(&elseBranch)));

      VList* vars = VList::singleton(variable);
      VList::pushFromIterator(VarSet::Iterator(*fv), vars);

      /* TODO: createNamingLiteral needs a formula to mark the colors correctly.
       * I'm not sure if it is the condition that should go here, but let's have that for now.
       */
      Formula* naming = new AtomicFormula(createNamingLiteral(condition, vars));

      Formula* thenDefinition = SubstHelper::apply(naming, thenSubst);
      Formula* elseDefinition = SubstHelper::apply(naming, elseSubst);

      enqueue(thenDefinition);
      enqueue(elseDefinition);

      introduceGenClause(negativeCondition, GenLit(thenDefinition, POSITIVE));
      introduceGenClause(positiveCondition, GenLit(elseDefinition, POSITIVE));

      while (List<LPair >::isNonEmpty(literals)) {
        LPair p = List<LPair >::pop(literals);
        Literal* literal = p.first;
        List<GenLit>* gls = p.second;

        LPair namePair = make_pair(literal, List<GenLit>::cons(GenLit(naming, NEGATIVE), gls));

        List<LPair>::push(namePair, processedLiterals);
      }
    }

    literals = processedLiterals;
    iteCounter++;
  }

  ASS(variables.isEmpty());
  ASS(conditions.isEmpty());
  ASS(thenBranches.isEmpty());
  ASS(elseBranches.isEmpty());

  LOG4("Found", matchVariables.size(), "variable(s) for matches inside", literal->toString());
  LOG3("Replacing it by", processedLiteral->toString(), "with variable substitutions");

  while (matchVariables.isNonEmpty()) {
    unsigned matchVar = matchVariables.pop();
    List<Formula *> *conditions = matchConditions.pop();
    List<TermList> *branches = matchBranches.pop();

    List<LPair> *processedLiterals(0);

    List<Formula *>::Iterator condIt(conditions);
    List<TermList>::Iterator branchIt(branches);

    while (List<LPair>::isNonEmpty(literals)) {
      LPair p = List<LPair>::pop(literals);
      Literal *literal = p.first;
      List<GenLit> *gls = p.second;

      while (condIt.hasNext()) {
        ASS(branchIt.hasNext());

        auto condition = condIt.next();
        auto branch = branchIt.next();
        enqueue(condition);

        GenLit negCondition = GenLit(condition, NEGATIVE);

        Substitution subst;
        subst.bind(matchVar, branch);

        Literal *branchLiteral = SubstHelper::apply(literal, subst);

        List<LPair>::push(make_pair(
                              branchLiteral, List<GenLit>::cons(negCondition, gls)),
                          processedLiterals);
      }
    }
    literals = processedLiterals;
  }

  ASS(matchVariables.isEmpty());
  ASS(matchConditions.isEmpty());
  ASS(matchBranches.isEmpty());

  while (occurrences.isNonEmpty()) {
    Occurrence occ = pop(occurrences);

    List<LPair >::Iterator lit(literals);
    while (lit.hasNext()) {
      LPair p = lit.next();
      Literal* literal = p.first;
      List<GenLit>* gls = p.second;

      Formula* f = new AtomicFormula(literal);

      enqueue(f);

      introduceExtendedGenClause(occ, List<GenLit>::cons(GenLit(f, occ.sign()), gls));
    }
  }
}

TermList NewCNF::findITEs(TermList ts, Stack<unsigned> &variables, Stack<Formula*> &conditions,
                          Stack<TermList> &thenBranches, Stack<TermList> &elseBranches,
                          Stack<unsigned> &matchVariables, Stack<List<Formula*>*> &matchConditions,
                          Stack<List<TermList>*> &matchBranches)
{
  CALL("NewCNF::findITEs");

  if (ts.isVar() || ts.term()->shared()) {
    return ts;
  }

  Term* term = ts.term();
  if (!term->isSpecial()) {
    Stack<TermList> arguments;

    Term::Iterator it(term);
    while (it.hasNext()) {
      arguments.push(findITEs(it.next(), variables, conditions, thenBranches,
        elseBranches, matchVariables, matchConditions, matchBranches));
    }

    unsigned proj;
    if (Theory::tuples()->findProjection(term->functor(), false, proj)) {
      TermList* arg = arguments.begin();
      if (arg->isTerm() && Theory::tuples()->isFunctor(arg->term()->functor())) {
        return *arg->term()->nthArgument(proj);
      }
    }

    return TermList(Term::create(term, arguments.begin()));
  }

  TermList sort;

  Term::SpecialTermData* sd = term->getSpecialData();
  switch (sd->getType()) {
    case Term::SF_FORMULA: {
      sort = AtomicSort::boolSort();
      conditions.push(sd->getFormula());
      thenBranches.push(TermList(Term::foolTrue()));
      elseBranches.push(TermList(Term::foolFalse()));
      break;
    }

    case Term::SF_ITE: {
      sort = sd->getSort();
      conditions.push(sd->getCondition());
      thenBranches.push(*term->nthArgument(0));
      elseBranches.push(*term->nthArgument(1));
      break;
    }

    case Term::SF_LET:
    case Term::SF_LET_TUPLE: {
      TermList contents = *term->nthArgument(0);
      TermList processedLet = eliminateLet(sd, contents);
      return findITEs(processedLet, variables, conditions, thenBranches,
        elseBranches, matchVariables, matchConditions, matchBranches);
    }

    case Term::SF_TUPLE: {
      TermList tupleTerm = TermList(sd->getTupleTerm());
      return findITEs(tupleTerm, variables, conditions, thenBranches,
                      elseBranches, matchVariables, matchConditions, matchBranches);
    }

    case Term::SF_MATCH: {
      sort = sd->getSort();
      auto matched = *term->nthArgument(0);
      List<Formula *> *mconditions(0);
      List<TermList> *mbranches(0);
      // for each case (p, t) with matched term m,
      // we create a condition m=p and a branch t
      for (unsigned int i = 1; i < term->arity(); i += 2) {
        auto pattern = *term->nthArgument(i);
        auto body = *term->nthArgument(i + 1);
        Formula *condition = new AtomicFormula(
            Literal::createEquality(POSITIVE, matched, pattern, sd->getMatchedSort()));
        List<Formula *>::push(condition, mconditions);
        List<TermList>::push(body, mbranches);
      }
      matchConditions.push(mconditions);
      matchBranches.push(mbranches);

      unsigned var = createFreshVariable(sort);
      matchVariables.push(var);
      return TermList(var, false);
    }

    default:
      ASSERTION_VIOLATION_REP(term->toString());
  }

  unsigned var = createFreshVariable(sort);

  variables.push(var);

  return TermList(var, false);
}

bool NewCNF::shouldInlineITE(unsigned iteCounter) {
  return iteCounter < _iteInliningThreshold;
}

unsigned NewCNF::createFreshVariable(TermList sort)
{
  CALL("NewCNF::createFreshVariable");

  ensureHavingVarSorts();

  _maxVar++;

  ALWAYS(_varSorts.insert(_maxVar, sort));

  return _maxVar;
}

void NewCNF::createFreshVariableRenaming(unsigned oldVar, unsigned freshVar)
{
  CALL("NewCNF::createFreshVariableRenaming");

  ensureHavingVarSorts();

  TermList sort;
  ALWAYS(_varSorts.find(oldVar, sort));
  if (!_varSorts.insert(freshVar, sort)) {
    ASSERTION_VIOLATION_REP(freshVar);
  }
  if (freshVar > _maxVar) {
    _maxVar = freshVar;
  }
}

void NewCNF::process(JunctionFormula *g, Occurrences &occurrences)
{
  CALL("NewCNF::process(JunctionFormula*)");

  LOG2("processJunction", g->toString());
  LOG2("occurrences.size", occurrences.size());

  FormulaList::Iterator fit(g->args());
  while (fit.hasNext()) {
    enqueue(fit.next());
  }

  SIGN formulaSign = g->connective() == OR ? POSITIVE : NEGATIVE;

  while (occurrences.isNonEmpty()) {
    Occurrence occ = pop(occurrences);

    List<GenLit>* gls = List<GenLit>::empty();
    FormulaList::Iterator git(g->args());
    while (git.hasNext()) {
      gls->push(GenLit(git.next(), occ.sign()), gls);
    }

    if (occ.sign() == formulaSign) {
      introduceExtendedGenClause(occ, gls);
    } else {
      List<GenLit>::Iterator glit(gls);
      while (glit.hasNext()) {
        introduceExtendedGenClause(occ, glit.next());
      }
    }
  }
}

void NewCNF::process(BinaryFormula* g, Occurrences &occurrences)
{
  CALL("NewCNF::process(BinaryFormula*)");

  LOG2("processBinary", g->toString());
  LOG2("occurrences.size", occurrences.size());

  ASS(g->connective() != IMP);

  SIGN formulaSign = g->connective() == IFF ? POSITIVE : NEGATIVE;

  Formula* lhs = g->left();
  Formula* rhs = g->right();

  enqueue(lhs);
  enqueue(rhs);

  while (occurrences.isNonEmpty()) {
    Occurrence occ = pop(occurrences);

    for (SIGN lhsSign : { NEGATIVE, POSITIVE }) {
      SIGN rhsSign = formulaSign == occ.sign() ? OPPOSITE(lhsSign) : lhsSign;
      introduceExtendedGenClause(occ, GenLit(lhs, lhsSign), GenLit(rhs, rhsSign));
    }
  }
}

void NewCNF::BindingStore::pushAndRememberWhileApplying(Binding b, BindingList* &lst)
{
  CALL("NewCNF::pushAndRememberWhileApplying");

  // turn b into a singleton substitution
  static Substitution subst;
  subst.bind(b.first,b.second);

  // to go through the bindings from the end, put them on a stack...
  static Stack<BindingList*> st(5);
  BindingList* traverse = lst;
  while (BindingList::isNonEmpty(traverse)) {
    st.push(traverse);
    traverse = traverse->tail();
  }

  /// keep applying subst
  Stack<BindingList*>::TopFirstIterator it(st);
  bool modified = false;
  while(it.hasNext()) {
    BindingList* cell = it.next();
    Binding someB = cell->head();
    Term* newTerm = SubstHelper::apply(someB.second, subst);
    if (modified || newTerm != someB.second) { // applying made a difference
      modified = true;
      lst = new BindingList(Binding(someB.first,newTerm),cell->tail());
      _stored.push(lst);
    }
  }
  pushAndRemember(b,lst);
  st.reset();
  subst.reset();
}

void NewCNF::processBoolVar(SIGN sign, unsigned var, Occurrences &occurrences)
{
  CALL("NewCNF::processBoolVar");

  LOG2("processBoolVar", (sign == POSITIVE ? "X" : "~X") + Int::toString(var));
  LOG2("occurrences.size", occurrences.size());

  /**
   * Note the following:
   * 1) ![X:$o]:( X | f(X)) <=> (1 | f(1)) & (0 | f(0)) <=> 1 & f(0) <=> f(0)
   * 2) ![X:$o]:(~X | f(X)) <=> (0 | f(1)) & (1 | f(0)) <=> f(1) & 1 <=> f(1)
   * 3) ?[X:$o]:( X | f(X)) <=> (1 | f(1)) | (0 | f(0)) <=> 1 | f(0) <=> 1
   * 3) ?[X:$o]:(~X | f(X)) <=> (0 | f(1)) | (1 | f(0)) <=> f(1) | 1 <=> 1
   *
   * It means the following. If the processed generalised literal is a boolean
   * variable, we can process each occurrence of it it two ways -- either by
   * discarding the occurrence's generalised clause all together, or removing
   * the generalised literal - variable from the occurrence. That depends on
   * whether the variable was skolemised in the clause. If it was (i.e. it was
   * under existential quantifier at some point), we remove the clause, otherwise
   * we remove the literal.
   */

  while (occurrences.isNonEmpty()) {
    Occurrence occ = pop(occurrences);
    SIGN occurrenceSign = (sign == occ.sign()) ? POSITIVE : NEGATIVE;

    bool bound = false;
    Term* skolem;

    // MS: can a non-fool binding ever map a bool var?
    BindingList::Iterator bit(occ.gc->bindings);
    while (bit.hasNext()) {
      Binding binding = bit.next();

      if (binding.first == var) {
        bound = true;
        skolem = binding.second;
        break;
      }
    }

    if (!bound) {
      BindingList::Iterator fbit(occ.gc->foolBindings);
      while (fbit.hasNext()) {
        Binding binding = fbit.next();

        if (binding.first == var) {
          bound = true;
          skolem = binding.second;
          break;
        }
      }
    }

    if (!bound) {
      Term* constant = (occurrenceSign == POSITIVE) ? Term::foolFalse() : Term::foolTrue();
      // MS: pushAndRemember is not enough; bindings could already be mentioning var on the rhs!
      // (BTW, scanning bindings for a second time, which is already ugly and potentially quadratic)
      _bindingStore.pushAndRememberWhileApplying(Binding(var, constant), occ.gc->bindings);
      removeGenLit(occ);
      continue;
    }

    bool isTrue  = env.signature->isFoolConstantSymbol(true,  skolem->functor());
    bool isFalse = env.signature->isFoolConstantSymbol(false, skolem->functor());

    if (isTrue || isFalse) {
      SIGN bindingSign = isTrue ? POSITIVE : NEGATIVE;
      if (occurrenceSign != bindingSign) {
        removeGenLit(occ);
      }
      continue;
    }

    introduceExtendedGenClause(occ, GenLit(new BoolTermFormula(TermList(var, false)), occurrenceSign));
  }
}

void NewCNF::processConstant(bool constant, Occurrences &occurrences)
{
  CALL("NewCNF::processConstant");

  while (occurrences.isNonEmpty()) {
    Occurrence occ = pop(occurrences);
    if (constant == (occ.sign() == POSITIVE)) {
      // constant is true -- remove the genclause that has it
    } else {
      // constant is false -- remove the occurrence of the constant
      removeGenLit(occ);
    }
  }
}

void NewCNF::processITE(Formula* condition, Formula* thenBranch, Formula* elseBranch, Occurrences &occurrences)
{
  CALL("NewCNF::processITE");

  enqueue(condition);
  enqueue(thenBranch);
  enqueue(elseBranch);

  while (occurrences.isNonEmpty()) {
    Occurrence occ = pop(occurrences);

    for (SIGN conditionSign : { NEGATIVE, POSITIVE }) {
      Formula* branch = conditionSign == NEGATIVE ? thenBranch : elseBranch;
      introduceExtendedGenClause(occ, GenLit(condition, conditionSign), GenLit(branch, occ.sign()));
    }
  }
}

void NewCNF::processMatch(Term::SpecialTermData *sd, Term *term, Occurrences &occurrences)
{
  CALL("NewCNF::processMatch");
  auto matched = *term->nthArgument(0);

  for (unsigned int i = 1; i < term->arity(); i += 2) {
    auto pattern = *term->nthArgument(i);
    auto body = *term->nthArgument(i + 1);
    Formula *condition = new AtomicFormula(
        Literal::createEquality(POSITIVE, matched, pattern, sd->getMatchedSort()));
    auto branch = BoolTermFormula::create(body);

    enqueue(condition);
    enqueue(branch);

    Occurrences::Iterator occit(occurrences);
    while (occit.hasNext()) {
      Occurrence occ = occit.next();
      introduceExtendedGenClause(occ, GenLit(condition, NEGATIVE), GenLit(branch, occ.sign()));
    }
  }
  while (occurrences.isNonEmpty()) {
    pop(occurrences);
  }
}

TermList NewCNF::eliminateLet(Term::SpecialTermData *sd, TermList contents)
{
  CALL("NewCNF::eliminateLet");

  ASS((sd->getType() == Term::SF_LET) || (sd->getType() == Term::SF_LET_TUPLE));

  unsigned symbol;
  VList* variables;
  TermList binding = sd->getBinding();

  if (sd->getType() == Term::SF_LET) {
    symbol = sd->getFunctor();
    variables = sd->getVariables();
  } else if (binding.isTerm() && binding.term()->isTuple()) {
    // binding of the form $let([x, y, z] := [a, b, c], ...) is processed
    // as $let(x := a, $let(y := b, $let(z := c, ...)))
    unsigned tupleFunctor = sd->getFunctor();
    VList* symbols = sd->getTupleSymbols();
    TermList bodySort = sd->getSort();

    OperatorType* tupleType = env.signature->getFunction(tupleFunctor)->fnType();

    Term* bindingTuple = binding.term()->getSpecialData()->getTupleTerm();
    unsigned arity = VList::length(symbols);
    VList::Iterator sit(symbols);
    Term::Iterator bit(bindingTuple);

    TermList processedContents = contents;
    TermList processedBinding;
    for (unsigned i = 0; i < arity - 1; i++) {
      ASS(bit.hasNext());
      ASS(sit.hasNext());
      Term* nestedLet = Term::createLet(sit.next(), 0, bit.next(), processedContents, bodySort);
      processedContents = TermList(nestedLet);
    }
    ASS(bit.hasNext());
    ASS(sit.hasNext());
    processedBinding = bit.next();
    symbol = sit.next();
    ASS(!sit.hasNext());
    ASS(!bit.hasNext());

    if (env.options->showPreprocessing()) {
      env.beginOutput();
      Term* tupleLet = Term::createTupleLet(tupleFunctor, symbols, binding, contents, tupleType->result());
      env.out() << "[PP] clausify (detuplify let) in:  " << tupleLet->toString() << endl;
      Term* processedLet = Term::createLet(symbol, 0, processedBinding, processedContents, bodySort);
      env.out() << "[PP] clausify (detuplify let) out: " << processedLet->toString() << endl;
      env.endOutput();
    }

    variables = VList::empty();
    contents = processedContents;
    binding = processedBinding;
  } else {
    unsigned tupleFunctor = sd->getFunctor();
    VList* symbols = sd->getTupleSymbols();
    TermList bodySort = sd->getSort();

    OperatorType* tupleType = env.signature->getFunction(tupleFunctor)->fnType();
    TermList tupleSort = tupleType->result();

    ASS_EQ(tupleType->arity(), VList::length(symbols));

    unsigned tuple = env.signature->addFreshFunction(0, "tuple");
    env.signature->getFunction(tuple)->setType(OperatorType::getConstantsType(tupleSort));

    TermList tupleTerm = TermList(Term::createConstant(tuple));

    TermList detupledContents = contents;

    for (unsigned proj = 0; proj < tupleType->arity(); proj++) {
      unsigned symbol = VList::nth(symbols, proj);
      bool isPredicate = tupleType->arg(proj) == AtomicSort::boolSort();

      unsigned projFunctor = Theory::tuples()->getProjectionFunctor(proj, tupleSort);
      Term* projectedArgument;
      if (isPredicate) {
        projectedArgument = Term::createFormula(new AtomicFormula(Literal::create1(projFunctor, 1, tupleTerm)));
      } else {
        projectedArgument = Term::create1(projFunctor, tupleTerm);
      }

      SymbolDefinitionInlining inlining(symbol, 0, TermList(projectedArgument), 0);
      detupledContents = inlining.process(detupledContents);
    }

    if (env.options->showPreprocessing()) {
      env.beginOutput();
      Term* tupleLet = Term::createTupleLet(tupleFunctor, symbols, binding, contents, tupleType->result());
      env.out() << "[PP] clausify (detuplify let) in:  " << tupleLet->toString() << endl;
      Term* processedLet = Term::createLet(tuple, 0, binding, detupledContents, bodySort);
      env.out() << "[PP] clausify (detuplify let) out: " << processedLet->toString() << endl;
      env.endOutput();
    }

    symbol = tuple;
    variables = VList::empty();
    contents = detupledContents;
  }

  bool inlineLet = env.options->getIteInlineLet();

  if (binding.isVar()) {
    inlineLet = true;
  } else {
//    Term* term = binding.term();
//    if (term->isSpecial()) {
//      Term::SpecialTermData* sd = term->getSpecialData();
//      if (sd->getType() == Term::SF_FORMULA) {
//        inlineLet = true;
//      }
//    }
//    if (term->shared()) {
//      // TODO: magic
////      if (term->weight() < 6) {
//        inlineLet = true;
////      }
//    } else if (term->isSpecial()) {
//      Term::SpecialTermData* sd = term->getSpecialData();
//      if (sd->getType() == Term::SF_FORMULA) {
//        Formula* f = sd->getFormula();
//        if ((f->connective() == LITERAL) && f->literal()->shared()) {
//          inlineLet = true;
//        }
//      }
//    }
  }

  TermList processedContents;
  if (inlineLet) {
    processedContents = inlineLetBinding(symbol, variables, binding, contents);
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] clausify (inline let) binding: " << binding.toString() << endl;
      env.out() << "[PP] clausify (inline let) in:  " << contents.toString() << endl;
      env.out() << "[PP] clausify (inline let) out: " << processedContents.toString() << endl;
      env.endOutput();
    }
  } else {
    processedContents = nameLetBinding(symbol, variables, binding, contents);
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] clausify (name let) binding: " << binding.toString() << endl;
      env.out() << "[PP] clausify (name let) in:  " << contents.toString() << endl;
      env.out() << "[PP] clausify (name let) out: " << processedContents.toString() << endl;
      env.endOutput();
    }
  }

  return processedContents;
}

void NewCNF::processLet(Term::SpecialTermData* sd, TermList contents, Occurrences &occurrences)
{
  CALL("NewCNF::processLet");

  ASS((sd->getType() == Term::SF_LET) || (sd->getType() == Term::SF_LET_TUPLE));

  TermList deletedContents = eliminateLet(sd, contents); // should be read "de-let-ed contents"
  Formula* deletedContentsFormula = BoolTermFormula::create(deletedContents);

  occurrences.replaceBy(deletedContentsFormula);

  enqueue(deletedContentsFormula, occurrences);
}

TermList NewCNF::nameLetBinding(unsigned symbol, VList* bindingVariables, TermList binding, TermList contents)
{
  CALL("NewCNF::nameLetBinding");

  VList* bindingFreeVars = VList::empty();
  FormulaVarIterator bfvi(&binding);
  while (bfvi.hasNext()) {
    unsigned var = bfvi.next();
    if (!VList::member(var, bindingVariables)) {
      VList::push(var,bindingFreeVars);
    }
  }

  bool isPredicate = binding.isTerm() && binding.term()->isBoolean();

  unsigned nameArity = VList::length(bindingVariables) + VList::length(bindingFreeVars);
  TermList nameSort;
  if (!isPredicate) {
    nameSort = env.signature->getFunction(symbol)->fnType()->result();
  }

  unsigned freshSymbol = symbol;

  bool renameSymbol = VList::isNonEmpty(bindingFreeVars);
  if (renameSymbol) {
    static Stack<TermList> sorts;
    sorts.reset();

    ensureHavingVarSorts();

    VList::Iterator vit(bindingFreeVars);
    while (vit.hasNext()) {
      unsigned var = vit.next();
      sorts.push(_varSorts.get(var, AtomicSort::defaultSort()));
    }

    if (isPredicate) {
      OperatorType* type = OperatorType::getPredicateType(nameArity, sorts.begin());
      freshSymbol = env.signature->addFreshPredicate(nameArity, "lG");
      env.signature->getPredicate(freshSymbol)->setType(type);
    } else {
      OperatorType* type = OperatorType::getFunctionType(nameArity, sorts.begin(), nameSort);
      freshSymbol = env.signature->addFreshFunction(nameArity, "lG");
      env.signature->getFunction(freshSymbol)->setType(type);
    }
  }


  Stack<TermList> arguments;
  VList::Iterator bfvit(bindingFreeVars);
  while (bfvit.hasNext()) {
    unsigned var = bfvit.next();
    arguments.push(TermList(var, false));
  }
  VList::Iterator vbit(bindingVariables);
  while (vbit.hasNext()) {
    unsigned var = vbit.next();
    arguments.push(TermList(var, false));
  }

  Term* freshApplication;

  if (isPredicate) {
    Literal* name = Literal::create(freshSymbol, nameArity, POSITIVE, false, arguments.begin());
    freshApplication = name;
    Formula* nameFormula = new AtomicFormula(name);

    Formula* formulaBinding = BoolTermFormula::create(binding);
    enqueue(formulaBinding);

    for (SIGN sign : { POSITIVE, NEGATIVE }) {
      introduceGenClause(GenLit(nameFormula, sign), GenLit(formulaBinding, OPPOSITE(sign)));
    }
  } else {
    TermList name = TermList(Term::create(freshSymbol, nameArity, arguments.begin()));
    freshApplication = name.term();
    Formula* nameFormula = new AtomicFormula(Literal::createEquality(POSITIVE, name, binding, nameSort));

    enqueue(nameFormula);

    introduceGenClause(GenLit(nameFormula, POSITIVE));
  }
  
  if (renameSymbol) {
    SymbolOccurrenceReplacement replacement(isPredicate, freshApplication, symbol, bindingVariables);
    return replacement.process(contents);
  }


  return contents;
}

TermList NewCNF::inlineLetBinding(unsigned symbol, VList* bindingVariables, TermList binding, TermList contents) {
  CALL("NewCNF::inlineLetBinding(TermList)");

  ensureHavingVarSorts();
  SymbolDefinitionInlining inlining(symbol, bindingVariables, binding, _maxVar);
  TermList inlinedContents = inlining.process(contents);

  List<pair<unsigned, unsigned>>::Iterator renamings(inlining.variableRenamings());
  while (renamings.hasNext()) {
    pair<unsigned, unsigned> renaming = renamings.next();
    createFreshVariableRenaming(renaming.first, renaming.second);
  }

  return Flattening::flatten(inlinedContents);
}

VarSet* NewCNF::freeVars(Formula* g)
{
  CALL("NewCNF::freeVars");

  LOG2("freeVars for", g->toString());

  VarSet* res;

  if (_freeVars.find(g,res)) {
    return res;
  }

  res = (VarSet*)VarSet::getFromIterator(FormulaVarIterator(g));

  _freeVars.insert(g,res);
  return res;
}

void NewCNF::ensureHavingVarSorts()
{
  CALL("NewCNF::ensureHavingVarSorts");

  if (!_collectedVarSorts) {
    SortHelper::collectVariableSorts(_beingClausified->formula(), _varSorts);
    _collectedVarSorts = true;
    _maxVar = 0;
    VirtualIterator<unsigned> vars = _varSorts.domain();
    while (vars.hasNext()) {
      unsigned var = vars.next();
      if (var > _maxVar) {
        _maxVar = var;
      }
    }
  }
}

Term* NewCNF::createSkolemTerm(unsigned var, VarSet* free, Formula *reuse_formula)
{
  CALL("NewCNF::createSkolemTerm");

  unsigned arity = free->size();

  ensureHavingVarSorts();
  TermList rangeSort=_varSorts.get(var, AtomicSort::defaultSort());
  static Stack<TermList> domainSorts;
  static Stack<TermList> fnArgs;
  ASS(domainSorts.isEmpty());
  ASS(fnArgs.isEmpty());

  NameReuse *name_reuse = (env.options->skolemReuse() && reuse_formula)
    ? NameReuse::skolemInstance()
    : nullptr;
  unsigned reused_symbol = 0;
  bool successfully_reused = false;
  vstring reuse_key;
  if(name_reuse) {
    reuse_key = name_reuse->key(reuse_formula);
    successfully_reused = name_reuse->get(reuse_key, reused_symbol);
  }
  if(successfully_reused)
    env.statistics->reusedSkolemFunctions++;

  // if we re-use a symbol, we _must_ close over free variables in some fixed order
  VirtualIterator<unsigned> keyOrderIt;
  if(name_reuse)
    keyOrderIt = name_reuse->freeVariablesInKeyOrder(reuse_formula);

  VarSet::Iterator vit(*free);
  while(name_reuse ? keyOrderIt.hasNext() : vit.hasNext()) {
    unsigned uvar = name_reuse ? keyOrderIt.next() : vit.next();
    domainSorts.push(_varSorts.get(uvar, AtomicSort::defaultSort()));
    fnArgs.push(TermList(uvar, false));
  }

  Term* res;
  bool isPredicate = (rangeSort == AtomicSort::boolSort());
  if (isPredicate) {
    unsigned pred = reused_symbol;
    if(!successfully_reused) {
      pred = Skolem::addSkolemPredicate(arity, domainSorts.begin(), var);
      if(name_reuse)
        name_reuse->put(reuse_key, pred);
      env.statistics->skolemFunctions++;
    }
    if(_beingClausified->derivedFromGoal()){
      env.signature->getPredicate(pred)->markInGoal();
    }
    res = Term::createFormula(new AtomicFormula(Literal::create(pred, arity, true, false, fnArgs.begin())));
  } else {
    unsigned fun = reused_symbol;
    if(!successfully_reused) {
      fun = Skolem::addSkolemFunction(arity, domainSorts.begin(), rangeSort, var);
      if(name_reuse)
        name_reuse->put(reuse_key, fun);
      env.statistics->skolemFunctions++;
    }
    if(_beingClausified->derivedFromGoal()){
      env.signature->getFunction(fun)->markInGoal();
    }
    if(_forInduction){
      env.signature->getFunction(fun)->markInductionSkolem();
    }
    res = Term::create(fun, arity, fnArgs.begin());
  }

  domainSorts.reset();
  fnArgs.reset();

  return res;
}

/**
 * Update the bindings of a generalized clause
 * in which a quantified formula g = (Quant Vars.Inner)
 * is being replaced by Inner. Each variable in Vars
 * will get a new binding. We try not to introduce
 * a new Skolem function unless it is necessary
 * so we cache results from skolemising previous
 * occurrences of g.
 */
void NewCNF::skolemise(QuantifiedFormula* g, BindingList*& bindings, BindingList*& foolBindings)
{
  CALL("NewCNF::skolemise");

  BindingList* processedBindings;
  BindingList* processedFoolBindings;

  if (!_skolemsByBindings.find(bindings, processedBindings) || !_foolSkolemsByBindings.find(foolBindings, processedFoolBindings)) {
    // first level cache miss, construct free variable set

    VarSet* frees = freeVars(g);

    static Stack<unsigned> toSubtract;
    toSubtract.reset();
    static Stack<unsigned> toAddOnTop;
    toAddOnTop.reset();

    BindingList::Iterator bIt(bindings);
    BindingList::Iterator fbIt(foolBindings);

    auto it = getConcatenatedIterator(bIt,fbIt);
    while(it.hasNext()) {
      Binding b = it.next();
      if (frees->member(b.first)) {
        toSubtract.push(b.first);      // because it's, in fact, bound
        VariableIterator vit(b.second);
        while (vit.hasNext()) {        // but depends on these free vars from above
          TermList t = vit.next();
          ASS(t.isVar());
          toAddOnTop.push(t.var());
        }
      }
    }

    Stack<unsigned>::Iterator toSubIt(toSubtract);
    Stack<unsigned>::Iterator toAddIt(toAddOnTop);

    VarSet* boundVars = VarSet::getFromIterator(toSubIt);
    VarSet* boundsDeps = VarSet::getFromIterator(toAddIt);

    VarSet* unboundFreeVars = frees->subtract(boundVars)->getUnion(boundsDeps);

    if (!_skolemsByFreeVars.find(unboundFreeVars, processedBindings) || !_foolSkolemsByFreeVars.find(unboundFreeVars, processedFoolBindings)) {
      // second level cache miss, let's do the actual skolemisation

      Substitution subst;
      Formula *reuse_formula = nullptr;
      VList *remainingVars = nullptr;
      SList *remainingSorts = nullptr;
      if(env.options->skolemReuse() && VList::length(g->vars()) <= 5) { // give up on skolemReuse for long quantifier blocks
        BindingList::Iterator bit(bindings);
        while (bit.hasNext()) {
          Binding b = bit.next();
          subst.bind(b.first, b.second);
        }
        reuse_formula = SubstHelper::apply(g, subst);
        // could be reuse_formula->vars() but SubstHelper might reorder them
        remainingVars = g->vars();
        remainingSorts = g->sorts();
      }

      processedBindings = nullptr;
      processedFoolBindings = nullptr;

      VList::Iterator vs(g->vars());
      while (vs.hasNext()) {
        unsigned var = vs.next();

        Term *skolem = createSkolemTerm(var, unboundFreeVars, reuse_formula);
        Binding binding(var, skolem);
        if (skolem->isSpecial()) {
          BindingList::push(binding, processedFoolBindings); // this cell will get destroyed when we clear the cache
        } else {
          BindingList::push(binding, processedBindings); // this cell will get destroyed when we clear the cache
        }

        // if we're re-using Skolems based on formulae,
        // we need to explicitly construct them: e.g. for ?[X, Y, Z]: F:
        // ?[X, Y, Z]: F,
        // ?[Y, Z]: F[X->sK0],
        // ?[Z]: F[X->sK0, Y->sK1],
        // but not F[X->sK0, Y->sK1, Z->sK2], since this doesn't need a Skolem term
        if(env.options->skolemReuse() && reuse_formula) {
          ASS(remainingVars != nullptr);
          remainingVars = remainingVars->tail();
          remainingSorts = remainingSorts ? remainingSorts->tail() : nullptr;
          if(VList::isNonEmpty(remainingVars)) {
            subst.bind(var, skolem);
            reuse_formula = new QuantifiedFormula(
              Connective::EXISTS,
              remainingVars,
              remainingSorts,
              SubstHelper::apply(reuse_formula->qarg(), subst)
            );
          }
        }
      }

      // store the results in the caches
      _skolemsByFreeVars.insert(unboundFreeVars, processedBindings);
      _foolSkolemsByFreeVars.insert(unboundFreeVars, processedFoolBindings);
    }

    _skolemsByBindings.insert(bindings, processedBindings);
    _foolSkolemsByBindings.insert(foolBindings, processedFoolBindings);
  }

  // extend the given binding
  BindingList::Iterator it(processedBindings);
  while (it.hasNext()) {
    _bindingStore.pushAndRemember(it.next(),bindings);
  }

  BindingList::Iterator fit(processedFoolBindings);
  while (fit.hasNext()) {
    _foolBindingStore.pushAndRemember(fit.next(),foolBindings);
  }
}

void NewCNF::process(QuantifiedFormula* g, Occurrences &occurrences)
{
  CALL("NewCNF::process(QuantifiedFormula*)");

  LOG2("processQuantified", g->toString());
  LOG2("occurreces", occurrences.size());

  // the skolem caches are empty
  ASS(_skolemsByBindings.isEmpty());
  ASS(_skolemsByFreeVars.isEmpty());
  ASS(_foolSkolemsByBindings.isEmpty());
  ASS(_foolSkolemsByFreeVars.isEmpty());

  // In the skolemising polarity introduce new skolems as you go
  // each occurrence may need a new set depending on bindings,
  // but let's try to share as much as possible
  Occurrences::Iterator occit(occurrences);
  while (occit.hasNext()) {
    Occurrence occ = occit.next();
    if ((occ.sign() == POSITIVE) == (g->connective() == EXISTS)) {
      skolemise(g, occ.gc->bindings, occ.gc->foolBindings);
    }
  }

  // empty the skolem caches
  _skolemsByBindings.reset();
  DHMap<VarSet*,BindingList*>::DelIterator dIt(_skolemsByFreeVars);
  while (dIt.hasNext()) {
    VarSet* vars;
    BindingList* bindings;
    dIt.next(vars,bindings);
    BindingList::destroy(bindings);
    dIt.del();
  }

  _foolSkolemsByBindings.reset();
  DHMap<VarSet*,BindingList*>::DelIterator fdit(_foolSkolemsByFreeVars);
  while (fdit.hasNext()) {
    VarSet* vars;
    BindingList* bindings;
    fdit.next(vars, bindings);
    BindingList::destroy(bindings);
    fdit.del();
  }

  // Note that the formula under quantifier reuses the quantified formula's occurrences
  enqueue(g->qarg(), occurrences);

  // Correct all the GenClauses to mention qarg instead of g
  occurrences.replaceBy(g->qarg());
}

void NewCNF::processBoolterm(TermList ts, Occurrences &occurrences)
{
  CALL("NewCNF::process(TermList)");

  if (ts.isVar()) {
    processBoolVar(POSITIVE, ts.var(), occurrences);
    return;
  }

  Term* term = ts.term();
  ASS_REP(term->isSpecial(), term->toString());

  Term::SpecialTermData* sd = term->getSpecialData();
  switch (sd->getType()) {
    case Term::SF_FORMULA:
      process(sd->getFormula(), occurrences);
      break;

    case Term::SF_ITE: {
      Formula* condition = sd->getCondition();

      Formula* left = BoolTermFormula::create(*term->nthArgument(LEFT));
      Formula* right = BoolTermFormula::create(*term->nthArgument(RIGHT));
      processITE(condition, left, right, occurrences);
      break;
    }

    case Term::SF_LET:
    case Term::SF_LET_TUPLE:
      processLet(sd, *term->nthArgument(0), occurrences);
      break;

    case Term::SF_MATCH: {
      processMatch(sd, term, occurrences);
      break;
    }

    default:
      ASSERTION_VIOLATION_REP(term->toString());
  }
}

/**
 * Stolen from Naming::getDefinitionLiteral
 */
Literal* NewCNF::createNamingLiteral(Formula* f, VList* free)
{
  CALL("NewCNF::createNamingLiteral");

  NameReuse *name_reuse = env.options->definitionReuse()
    ? NameReuse::definitionInstance()
    : nullptr;
  unsigned reused_symbol = 0;
  bool successfully_reused = false;
  vstring reuse_key;
  if(name_reuse) {
    reuse_key = name_reuse->key(f);
    successfully_reused = name_reuse->get(reuse_key, reused_symbol);
  }
  if(successfully_reused)
    env.statistics->reusedFormulaNames++;

  unsigned length = VList::length(free);
  unsigned pred = reused_symbol;
  if(!successfully_reused) {
    pred = env.signature->addNamePredicate(length);
    env.statistics->formulaNames++;
    if(name_reuse)
      name_reuse->put(reuse_key, pred);
  }

  Signature::Symbol* predSym = env.signature->getPredicate(pred);

  if (!successfully_reused && env.colorUsed) {
    Color fc = f->getColor();
    if (fc != COLOR_TRANSPARENT) {
      predSym->addColor(fc);
    }
    if (f->getSkip()) {
      predSym->markSkip();
    }
  }

  static Stack<TermList> domainSorts;
  static Stack<TermList> predArgs;
  domainSorts.reset();
  predArgs.reset();

  ensureHavingVarSorts();

  // if we re-use a symbol, we _must_ close over free variables in some fixed order
  VirtualIterator<unsigned> keyOrderIt;
  if(name_reuse)
    keyOrderIt = name_reuse->freeVariablesInKeyOrder(f);

  VList::Iterator vit(free);
  while (name_reuse ? keyOrderIt.hasNext() : vit.hasNext()) {
    unsigned uvar = name_reuse ? keyOrderIt.next() : vit.next();
    domainSorts.push(_varSorts.get(uvar, AtomicSort::defaultSort()));
    predArgs.push(TermList(uvar, false));
  }
  VList::destroy(free);

  if(!successfully_reused)
    predSym->setType(OperatorType::getPredicateType(length, domainSorts.begin()));

  return Literal::create(pred, length, true, false, predArgs.begin());
}

/**
 * Formula g with occurrences is being named.
 * Introduce a new symbol skP, replace the occurrences by skP(U,V,..)
 * where U,V,.. are free variables of g and
 * and return skP(U,V,..).
 *
 * Occurrence lists in occurrences get destroyed.
 */
void NewCNF::nameSubformula(Formula* g, Occurrences &occurrences)
{
  CALL("NewCNF::nameSubformula");

  LOG2("nameSubformula", g->toString());
  LOG2("occurrences", occurrences.size());

  VList* fv = VList::empty();
  VList::pushFromIterator(VarSet::Iterator(*freeVars(g)), fv);

  Literal* naming = createNamingLiteral(g, fv);
  Formula* name = new AtomicFormula(naming);

  occurrences.replaceBy(name);

  enqueue(g);

  bool occurs[2] = { false, false };
  Occurrences::Iterator occit(occurrences);
  while (occit.hasNext()) {
    Occurrence occ = occit.next();
    occurs[occ.sign()] = true;
    if (occurs[POSITIVE] && occurs[NEGATIVE]) {
      break;
    }
  }

  for (SIGN sign : { NEGATIVE, POSITIVE }) {
    // One could also consider the case where (part of) the bindings goes to the definition
    // which perhaps allows us to the have a skolem predicate with fewer arguments
    if (occurs[sign] && !_already_seen[sign].contains(naming)) {
      introduceGenClause(GenLit(name, OPPOSITE(sign)), GenLit(g, sign));
      _already_seen[sign].insert(naming);
    }
  }
}

void NewCNF::process(Formula* g, Occurrences &occurrences)
{
  CALL("NewCNF::process");

  switch (g->connective()) {
    case AND:
    case OR:
      process(static_cast<JunctionFormula*>(g), occurrences);
      break;

    case IFF:
    case XOR:
      process(static_cast<BinaryFormula*>(g), occurrences);
      break;

    case FORALL:
    case EXISTS:
      process(static_cast<QuantifiedFormula*>(g),occurrences);
      break;

    case BOOL_TERM:
      processBoolterm(g->getBooleanTerm(), occurrences);
      break;

    case LITERAL:
      process(g->literal(),occurrences);
      break;

    case NOT:
      ASS_REP(g->uarg()->connective() == BOOL_TERM, g->uarg()->toString());
      ASS_REP(g->uarg()->getBooleanTerm().isVar(),  g->uarg()->toString());
      processBoolVar(NEGATIVE, g->uarg()->getBooleanTerm().var(), occurrences);
      break;

    case TRUE:
    case FALSE:
      processConstant(g->connective() == TRUE, occurrences);
      break;

    default:
      ASSERTION_VIOLATION_REP(g->toString());
  }
}

void NewCNF::toClauses(SPGenClause gc, Stack<Clause*>& output)
{
  CALL("NewCNF::toClauses");

  Stack<unsigned> variables;
  Stack<Formula*> skolems;

  BindingList::Iterator bit(gc->foolBindings);
  while (bit.hasNext()) {
    Binding b = bit.next();
    unsigned var = b.first;
    Term* skolem = b.second;
    variables.push(var);
    ASS_REP(skolem->isFormula(), skolem->toString());
    Formula* f = skolem->getSpecialData()->getFormula();
    ASS_REP(f->connective() == LITERAL, f->toString());
    skolems.push(f);
  }

  List<GenLit>* initLiterals(0);
  List<GenLit>::pushFromIterator(gc->genLiterals(), initLiterals);

  List<List<GenLit>*>* genClauses = new List<List<GenLit>*>(initLiterals);

  unsigned iteCounter = 0;
  while (variables.isNonEmpty()) {
    unsigned variable = variables.pop();
    Formula* skolem   = skolems.pop();

    Substitution thenSubst;
    thenSubst.bind(variable, Term::foolTrue());

    Substitution elseSubst;
    elseSubst.bind(variable, Term::foolFalse());

    List<List<GenLit>*>* processedGenClauses(0);

    if (shouldInlineITE(iteCounter)) {
      while (List<List<GenLit>*>::isNonEmpty(genClauses)) {
        List<GenLit>* gls = List<List<GenLit>*>::pop(genClauses);

        bool occurs = false;
        // We might have a predicate skolem binding for a variable that does not
        // occur in the generalised clause.
        // TODO: optimize?
        List<GenLit>::Iterator glsit(gls);
        while (glsit.hasNext()) {
          GenLit gl = glsit.next();
          if (formula(gl)->isFreeVariable(variable)) {
            occurs = true;
            break;
          }
        }

        if (!occurs) {
          List<List<GenLit>*>::push(gls, processedGenClauses);
          continue;
        }

        List<GenLit>* thenGls(0);
        if (mapSubstitution(gls, thenSubst, false, thenGls)) {
          List<List<GenLit>*>::push(List<GenLit>::cons(GenLit(skolem, NEGATIVE), thenGls),
                                    processedGenClauses);
        }

        List<GenLit>* elseGls(0);
        if (mapSubstitution(gls, elseSubst, false, elseGls)) {
          List<List<GenLit>*>::push(List<GenLit>::cons(GenLit(skolem, POSITIVE), elseGls),
                                    processedGenClauses);
        }
      }
    } else {
      VList* vars = VList::singleton(variable);
      VList::pushFromIterator(FormulaVarIterator(skolem), vars);
      Formula* naming = new AtomicFormula(createNamingLiteral(skolem, vars));

      Substitution skolemSubst;
      skolemSubst.bind(variable, Term::createFormula(skolem));

      bool addedDefinition = false;
      while (List<List<GenLit>*>::isNonEmpty(genClauses)) {
        List<GenLit>* gls = List<List<GenLit>*>::pop(genClauses);

        bool occurs = false;
        // We might have a predicate skolem binding for a variable that does not
        // occur in the generalised clause.
        // TODO: optimize?
        List<GenLit>::Iterator glsit(gls);
        while (glsit.hasNext()) {
          GenLit gl = glsit.next();
          if (formula(gl)->isFreeVariable(variable)) {
            occurs = true;
            break;
          }
        }

        if (!occurs) {
          List<List<GenLit>*>::push(gls, processedGenClauses);
          continue;
        }

        List<GenLit>* skolemGls(0);
        ALWAYS(mapSubstitution(gls, skolemSubst, true, skolemGls));
        List<List<GenLit>*>::push(List<GenLit>::cons(GenLit(naming, NEGATIVE), skolemGls),
                                  processedGenClauses);

        if (!addedDefinition) {
          GenLit thenNaming = GenLit(SubstHelper::apply(naming, thenSubst), POSITIVE);
          GenLit elseNaming = GenLit(SubstHelper::apply(naming, elseSubst), POSITIVE);

          List<GenLit>* thenDefinition = new List<GenLit>(GenLit(skolem, NEGATIVE), new List<GenLit>(thenNaming, 0));
          List<GenLit>* elseDefinition = new List<GenLit>(GenLit(skolem, POSITIVE), new List<GenLit>(elseNaming, 0));

          List<List<GenLit>*>::push(thenDefinition, processedGenClauses);
          List<List<GenLit>*>::push(elseDefinition, processedGenClauses);

          addedDefinition = true;
        }
      }
    }

    genClauses = processedGenClauses;
    iteCounter++;
  }

#if LOGGING
  cout << endl << "----------------- CNF ------------------" << endl;
#endif
  while (List<List<GenLit>*>::isNonEmpty(genClauses)) {
    List<GenLit>* gls = List<List<GenLit>*>::pop(genClauses);
    SPGenClause genClause = makeGenClause(gls, gc->bindings, BindingList::empty());
    if (genClause->valid) {
      Clause* clause = toClause(genClause);
      LOG1(clause->toString());
      output.push(clause);
    } else {
      LOG2(genClause->toString(), "was removed as it contains a tautology");
    }
  }
#if LOGGING
  cout << "----------------- CNF ------------------" << endl << endl;
#endif
}

bool NewCNF::mapSubstitution(List<GenLit>* clause, Substitution subst, bool onlyFormulaLevel, List<GenLit>* &output)
{
  CALL("NewCNF::mapSubstitution");

  List<GenLit>::Iterator it(clause);
  while (it.hasNext()) {
    GenLit gl = it.next();
    Formula* f = (onlyFormulaLevel && (formula(gl)->connective() == LITERAL))
                  ? formula(gl)
                  : SubstHelper::apply(formula(gl), subst);

    switch (f->connective()) {
      case TRUE:
      case FALSE: {
        SIGN fSign = f->connective() == TRUE ? POSITIVE : NEGATIVE;
        if (sign(gl) == fSign) {
          return false;
        } else {
          continue;
        }
      }

      case BOOL_TERM:
      case LITERAL: {
        List<GenLit>::push(GenLit(f, sign(gl)), output);
        break;
      }

      default:
        ASSERTION_VIOLATION_REP(f->toString());
    }
  }

  return true;
}

Clause* NewCNF::toClause(SPGenClause gc)
{
  CALL("NewCNF::toClause");

  Substitution* subst;

  if (!_substitutionsByBindings.find(gc->bindings, subst)) {
    subst = new Substitution();
    BindingList::Iterator bit(gc->bindings);
    while (bit.hasNext()) {
      Binding b = bit.next();
      subst->bind(b.first, b.second);
    }
    _substitutionsByBindings.insert(gc->bindings, subst);
  }

  static Stack<Literal*> properLiterals;
  ASS(properLiterals.isEmpty());

  GenClause::Iterator lit = gc->genLiterals();
  while (lit.hasNext()) {
    GenLit gl = lit.next();
    Formula* g = formula(gl);

    ASS_REP(g->connective() == LITERAL, gc->toString());
    ASS_REP(g->literal()->shared(), g->toString());
    ASS_REP((SIGN)g->literal()->polarity() == POSITIVE, g->toString());

    Literal* l = g->literal()->apply(*subst);
    if (sign(gl) == NEGATIVE) {
      l = Literal::complementaryLiteral(l);
    }

    properLiterals.push(l);
  }

  Clause* clause = new(gc->size()) Clause(gc->size(),FormulaTransformation(InferenceRule::CLAUSIFY,_beingClausified));
  for (int i = gc->size() - 1; i >= 0; i--) {
    (*clause)[i] = properLiterals[i];
  }

  properLiterals.reset();

  return clause;
}

}
