/**
 * @file NewCNF.cpp
 * Implements class NewCNF implementing the new CNF transformation.
 * @since 19/11/2015 Manchester
 */

#include "Debug/Tracer.hpp"

#include "Kernel/Sorts.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/TermIterators.hpp"
#include "Shell/Flattening.hpp"
#include "Shell/Skolem.hpp"
#include "Shell/Options.hpp"
#include "Shell/SymbolOccurrenceReplacement.hpp"
#include "Shell/SymbolDefinitionInlining.hpp"

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
      Inference* inf = new Inference1(Inference::CLAUSIFY,unit);
      Clause* clause = new(0) Clause(0, unit->inputType(),inf);
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
  _freeVars.reset();

  ASS(_queue.isEmpty());
  ASS(_occurrences.isEmpty());
}

void NewCNF::process(Literal* literal, Occurrences &occurrences) {
  CALL("NewCNF::process(Literal*)");

  LOG2("process(Literal*)", literal->toString());
  LOG2("occurrences.size", occurrences.size());

//  ASS_REP(!literal->shared(), literal->toString());
  if (literal->shared()) {
    return;
  }

  Stack<unsigned> variables;
  Stack<Formula*> conditions;
  Stack<TermList> thenBranches;
  Stack<TermList> elseBranches;

  Stack<TermList> arguments;
  Term::Iterator ait(literal);
  while (ait.hasNext()) {
    arguments.push(findITEs(ait.next(), variables, conditions, thenBranches, elseBranches));
  }
  Literal* processedLiteral = Literal::create(literal, arguments.begin());

  List<pair<Literal*, List<GenLit>*> >* literals(0);
  literals = literals->cons(make_pair(processedLiteral, List<GenLit>::empty()));

  LOG4("Found", variables.size(), "variable(s) inside", literal->toString());
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

    List<pair<Literal*, List<GenLit>*> >* processedLiterals(0);

    if (shouldInlineITE(iteCounter)) {
      while (List<pair<Literal*, List<GenLit>*> >::isNonEmpty(literals)) {
        pair<Literal*, List<GenLit>*> p = List<pair<Literal*, List<GenLit>*> >::pop(literals);
        Literal* literal = p.first;
        List<GenLit>* gls = p.second;

        Literal* thenLiteral = SubstHelper::apply(literal, thenSubst);
        Literal* elseLiteral = SubstHelper::apply(literal, elseSubst);

        pair<Literal*, List<GenLit>*> thenPair = make_pair(thenLiteral, gls->cons(negativeCondition));
        pair<Literal*, List<GenLit>*> elsePair = make_pair(elseLiteral, gls->cons(positiveCondition));

        processedLiterals = processedLiterals->cons(thenPair);
        processedLiterals = processedLiterals->cons(elsePair);
      }
    } else {
      IntList::Iterator branchesFreeVars(thenBranch.freeVariables()->append(elseBranch.freeVariables()));
      VarSet* fv = (VarSet*) freeVars(condition)->getUnion(VarSet::getFromIterator(branchesFreeVars));

      List<unsigned>* vars = new List<unsigned>(variable);
      List<unsigned>::pushFromIterator(VarSet::Iterator(*fv), vars);

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

      while (List<pair<Literal*, List<GenLit>*> >::isNonEmpty(literals)) {
        pair<Literal*, List<GenLit>*> p = List<pair<Literal*, List<GenLit>*> >::pop(literals);
        Literal* literal = p.first;
        List<GenLit>* gls = p.second;

        pair<Literal*, List<GenLit>*> namePair = make_pair(literal, gls->cons(GenLit(naming, NEGATIVE)));

        processedLiterals = processedLiterals->cons(namePair);
      }
    }

    literals = processedLiterals;
    iteCounter++;
  }

  ASS(variables.isEmpty());
  ASS(conditions.isEmpty());
  ASS(thenBranches.isEmpty());
  ASS(elseBranches.isEmpty());

  while (occurrences.isNonEmpty()) {
    Occurrence occ = pop(occurrences);

    List<pair<Literal*, List<GenLit>*> >::Iterator lit(literals);
    while (lit.hasNext()) {
      pair<Literal*, List<GenLit>*> p = lit.next();
      Literal* literal = p.first;
      List<GenLit>* gls = p.second;

      Formula* f = new AtomicFormula(literal);

      enqueue(f);

      introduceExtendedGenClause(occ.gc, occ.position, gls->cons(GenLit(f, occ.sign())));
    }
  }
}

TermList NewCNF::findITEs(TermList ts, Stack<unsigned> &variables, Stack<Formula*> &conditions,
                          Stack<TermList> &thenBranches, Stack<TermList> &elseBranches)
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
      arguments.push(findITEs(it.next(), variables, conditions, thenBranches, elseBranches));
    }

    return TermList(Term::create(term, arguments.begin()));
  }

  unsigned sort;

  Term::SpecialTermData* sd = term->getSpecialData();
  switch (sd->getType()) {
    case Term::SF_FORMULA: {
      sort = Sorts::SRT_BOOL;
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
      NOT_IMPLEMENTED;

    default:
      ASSERTION_VIOLATION;
  }

  unsigned var = createFreshVariable(sort);

  variables.push(var);

  return TermList(var, false);
}

bool NewCNF::shouldInlineITE(unsigned iteCounter) {
  int threshold = env.options->getIteInliningThreshold();
  if (threshold < 0) {
    return true;
  }
  if (threshold == 0) {
    return false;
  }
  return iteCounter < threshold;
}

unsigned NewCNF::createFreshVariable(unsigned sort)
{
  CALL("NewCNF::createFreshVariable");

  ensureHavingVarSorts();

  unsigned maxVar = 0;

  VirtualIterator<unsigned> vars = _varSorts.domain();
  while (vars.hasNext()) {
    unsigned var = vars.next();
    if (var > maxVar) {
      maxVar = var;
    }
  }

  ALWAYS(_varSorts.insert(maxVar + 1, sort));

  return maxVar + 1;
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
      introduceExtendedGenClause(occ.gc, occ.position, gls);
    } else {
      List<GenLit>::Iterator glit(gls);
      while (glit.hasNext()) {
        introduceExtendedGenClause(occ.gc, occ.position, glit.next());
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

  if (lhs->connective() == BOOL_TERM && rhs->connective() == BOOL_TERM) {
    TermList lhsTerm = lhs->getBooleanTerm();
    TermList rhsTerm = rhs->getBooleanTerm();

    Literal *equalityLiteral = Literal::createEquality(formulaSign, lhsTerm, rhsTerm, Sorts::SRT_BOOL);
    Formula *equality = new AtomicFormula(equalityLiteral);

    occurrences.replaceBy(equality);

    enqueue(equality, occurrences);

    return;
  }

  enqueue(lhs);
  enqueue(rhs);

  while (occurrences.isNonEmpty()) {
    Occurrence occ = pop(occurrences);

    for (SIGN lhsSign : { NEGATIVE, POSITIVE }) {
      SIGN rhsSign = formulaSign == occ.sign() ? OPPOSITE(lhsSign) : lhsSign;
      introduceExtendedGenClause(occ.gc, occ.position, GenLit(lhs, lhsSign), GenLit(rhs, rhsSign));
    }
  }
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
      Term* constant = (occurrenceSign == POSITIVE) ? Term::foolFalse() : Term::foolTrue();
      BindingList::push(Binding(var, constant), occ.gc->bindings);
      removeGenLit(occ.gc, occ.position);
      continue;
    }

    bool isTrue  = env.signature->isFoolConstantSymbol(true,  skolem->functor());
    bool isFalse = env.signature->isFoolConstantSymbol(false, skolem->functor());

    if (isTrue || isFalse) {
      SIGN bindingSign = isTrue ? POSITIVE : NEGATIVE;
      if (occurrenceSign != bindingSign) {
        removeGenLit(occ.gc, occ.position);
      }
      continue;
    }

    introduceExtendedGenClause(occ.gc, occ.position, GenLit(new BoolTermFormula(TermList(var, false)), occurrenceSign));
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
      introduceExtendedGenClause(occ.gc, occ.position, GenLit(condition, conditionSign), GenLit(branch, occ.sign()));
    }
  }
}

void NewCNF::processLet(unsigned symbol, Formula::VarList* bindingVariables, TermList binding, TermList contents, Occurrences &occurrences)
{
  CALL("NewCNF::processLet");

  bool inlineLet = false;

  if (binding.isVar()) {
    inlineLet = true;
  } else {
    inlineLet = env.options->getIteInlineLet();
//    Term* term = binding.term();
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
    processedContents = inlineLetBinding(symbol, bindingVariables, binding, contents);
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] clausify (inline let) binding: " << binding.toString() << endl;
      env.out() << "[PP] clausify (inline let) in:  " << contents.toString() << endl;
      env.out() << "[PP] clausify (inline let) out: " << processedContents.toString() << endl;
      env.endOutput();
    }
  } else {
    processedContents = nameLetBinding(symbol, bindingVariables, binding, contents);
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] clausify (name let) binding: " << binding.toString() << endl;
      env.out() << "[PP] clausify (name let) in:  " << contents.toString() << endl;
      env.out() << "[PP] clausify (name let) out: " << processedContents.toString() << endl;
      env.endOutput();
    }
  }

  Formula* processedContentsFormula = BoolTermFormula::create(processedContents);

  occurrences.replaceBy(processedContentsFormula);

  process(processedContentsFormula, occurrences);
}

TermList NewCNF::nameLetBinding(unsigned symbol, Formula::VarList* bindingVariables, TermList binding, TermList contents)
{
  CALL("NewCNF::nameLetBinding");

  Formula::VarList* bindingFreeVars(0);
  Formula::VarList::Iterator bfvi(binding.freeVariables());
  while (bfvi.hasNext()) {
    int var = bfvi.next();
    if (!bindingVariables->member(var)) {
      bindingFreeVars = new Formula::VarList(var, bindingFreeVars);
    }
  }

  bool isPredicate = binding.isTerm() && binding.term()->isBoolean();

  unsigned nameArity = (unsigned) bindingVariables->length() + bindingFreeVars->length();
  unsigned nameSort;
  if (!isPredicate) {
    nameSort = env.signature->getFunction(symbol)->fnType()->result();
  }

  unsigned freshSymbol = symbol;

  bool renameSymbol = Formula::VarList::isNonEmpty(bindingFreeVars);
  if (renameSymbol) {
    static Stack<unsigned> sorts;
    sorts.reset();

    ensureHavingVarSorts();

    IntList::Iterator vit(bindingFreeVars);
    while (vit.hasNext()) {
      unsigned var = (unsigned) vit.next();
      sorts.push(_varSorts.get(var, Sorts::SRT_DEFAULT));
    }

    if (isPredicate) {
      PredicateType* type = new PredicateType(nameArity, sorts.begin());
      freshSymbol = env.signature->addFreshPredicate(nameArity, "lG");
      env.signature->getPredicate(freshSymbol)->setType(type);
    } else {
      FunctionType* type = new FunctionType(nameArity, sorts.begin(), nameSort);
      freshSymbol = env.signature->addFreshFunction(nameArity, "lG");
      env.signature->getFunction(freshSymbol)->setType(type);
    }
  }

  Formula::VarList* variables = bindingFreeVars->append(bindingVariables);

  Stack<TermList> arguments;
  Formula::VarList::Iterator vit(variables);
  while (vit.hasNext()) {
    unsigned var = (unsigned)vit.next();
    arguments.push(TermList(var, false));
  }

  if (isPredicate) {
    Formula* formulaBinding = BoolTermFormula::create(binding);

    enqueue(formulaBinding);

    Literal* name = Literal::create(freshSymbol, nameArity, POSITIVE, false, arguments.begin());
    Formula* nameFormula = new AtomicFormula(name);

    for (SIGN sign : { POSITIVE, NEGATIVE }) {
      introduceGenClause(GenLit(nameFormula, sign), GenLit(formulaBinding, OPPOSITE(sign)));
    }
  } else {
    TermList name = TermList(Term::create(freshSymbol, nameArity, arguments.begin()));
    Formula* nameFormula = new AtomicFormula(Literal::createEquality(POSITIVE, name, binding, nameSort));

    enqueue(nameFormula);

    introduceGenClause(GenLit(nameFormula, POSITIVE));
  }

  if (renameSymbol) {
    SymbolOccurrenceReplacement replacement(isPredicate, symbol, freshSymbol, bindingFreeVars);
    return replacement.process(contents);
  }

  return contents;
}

TermList NewCNF::inlineLetBinding(unsigned symbol, Formula::VarList* bindingVariables, TermList binding, TermList contents) {
  CALL("NewCNF::inlineLetBinding(TermList)");

  SymbolDefinitionInlining inlining(symbol, bindingVariables, binding);
  return Flattening::flatten(inlining.process(contents));
}

NewCNF::VarSet* NewCNF::freeVars(Formula* g)
{
  CALL("NewCNF::freeVars");

  LOG2("freeVars for", g->toString());

  VarSet* res;

  if (_freeVars.find(g,res)) {
    return res;
  }

  Formula::VarList::Iterator fv(g->freeVariables());
  res = (VarSet*) VarSet::getFromIterator(fv);

  _freeVars.insert(g,res);
  return res;
}

void NewCNF::ensureHavingVarSorts()
{
  CALL("NewCNF::ensureHavingVarSorts");

  if (_varSorts.size() == 0) {
    SortHelper::collectVariableSorts(_beingClausified->formula(), _varSorts);
  }
}

Term* NewCNF::createSkolemTerm(unsigned var, VarSet* free)
{
  CALL("NewCNF::createSkolemTerm");

  unsigned arity = free->size();

  ensureHavingVarSorts();
  unsigned rangeSort=_varSorts.get(var, Sorts::SRT_DEFAULT);
  static Stack<unsigned> domainSorts;
  static Stack<TermList> fnArgs;
  ASS(domainSorts.isEmpty());
  ASS(fnArgs.isEmpty());

  VarSet::Iterator vit(*free);
  while(vit.hasNext()) {
    unsigned uvar = vit.next();
    domainSorts.push(_varSorts.get(uvar, Sorts::SRT_DEFAULT));
    fnArgs.push(TermList(uvar, false));
  }

  Term* res;
  bool isPredicate = rangeSort == Sorts::SRT_BOOL;
  if (isPredicate) {
    unsigned pred = Skolem::addSkolemPredicate(arity, domainSorts.begin(), var);
    res = Term::createFormula(new AtomicFormula(Literal::create(pred, arity, true, false, fnArgs.begin())));
  } else {
    unsigned fun = Skolem::addSkolemFunction(arity, domainSorts.begin(), rangeSort, var);
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
 * with get a new binding. We try not to introduce
 * a new Skolem function unless it is necessary
 * so we cache results from skolemising previous
 * occurrences of g.
 */
void NewCNF::skolemise(QuantifiedFormula* g, BindingList*& bindings)
{
  CALL("NewCNF::skolemise");

  BindingList* processedBindings;

  if (!_skolemsByBindings.find(bindings, processedBindings)) {
    // first level cache miss, construct free variable set

    BindingList::Iterator bIt(bindings);
    VarSet* boundVars = (VarSet*) VarSet::getFromIterator(getMappingIterator(bIt, BindingGetVarFunctor()));
    VarSet* unboundFreeVars = (VarSet*) freeVars(g)->subtract(boundVars);

    if (!_skolemsByFreeVars.find(unboundFreeVars, processedBindings)) {
      // second level cache miss, let's do the actual skolemisation

      processedBindings = nullptr;

      Formula::VarList::Iterator vs(g->vars());
      while (vs.hasNext()) {
        unsigned var = (unsigned)vs.next();
        Term* skolemTerm = createSkolemTerm(var, unboundFreeVars);
        BindingList::push(Binding(var,skolemTerm), processedBindings);
      }

      // store the results in the caches
      _skolemsByFreeVars.insert(unboundFreeVars, processedBindings);
    }

    _skolemsByBindings.insert(bindings, processedBindings);
  }

  // extend the given binding
  BindingList::Iterator it(processedBindings);
  while (it.hasNext()) {
    BindingList::push(it.next(),bindings);
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

  // In the skolemising polarity introduce new skolems as you go
  // each occurrence may need a new set depending on bindings,
  // but let's try to share as much as possible
  Occurrences::Iterator occit(occurrences);
  while (occit.hasNext()) {
    Occurrence occ = occit.next();
    if ((occ.sign() == POSITIVE) == (g->connective() == EXISTS)) {
      skolemise(g, occ.gc->bindings);
    }
  }

  // empty the skolem caches
  _skolemsByBindings.reset();
  DHMap<VarSet*,BindingList*>::DelIterator dIt(_skolemsByFreeVars);
  while (dIt.hasNext()) {
    VarSet* vars;
    BindingList* bindings;
    dIt.next(vars,bindings);
    bindings->destroy();
    dIt.del();
  }

  // Note that the formula under quantifier reuses the quantified formula's occurrences
  enqueue(g->qarg(), occurrences);

  // Correct all the GenClauses to mention qarg instead of g
  occurrences.replaceBy(g->qarg());
}

void NewCNF::process(TermList ts, Occurrences &occurrences)
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
    case Term::SF_FORMULA: {
      process(sd->getFormula(), occurrences);
      break;
    }

    case Term::SF_ITE: {
      Formula* condition = sd->getCondition();

      Formula* branch[2];
      for (SIDE side : { LEFT, RIGHT }) {
        branch[side] = BoolTermFormula::create(*term->nthArgument(side));
      }

      processITE(condition, branch[LEFT], branch[RIGHT], occurrences);
      break;
    }

    case Term::SF_LET: {
      unsigned symbol = sd->getFunctor();
      Formula::VarList* variables = sd->getVariables();
      TermList binding = sd->getBinding();
      TermList contents = *term->nthArgument(0);

      processLet(symbol, variables, binding, contents, occurrences);
      break;
    }

    default:
      ASSERTION_VIOLATION_REP(term->toString());
  }
}

/**
 * Stolen from Naming::getDefinitionLiteral
 */
Literal* NewCNF::createNamingLiteral(Formula* f, List<unsigned>* free)
{
  CALL("NewCNF::createNamingLiteral");

  unsigned length = (unsigned) free->length();
  unsigned pred = env.signature->addNamePredicate(length);
  Signature::Symbol* predSym = env.signature->getPredicate(pred);

  if (env.colorUsed) {
    Color fc = f->getColor();
    if (fc != COLOR_TRANSPARENT) {
      predSym->addColor(fc);
    }
    if (f->getSkip()) {
      predSym->markSkip();
    }
  }

  static Stack<unsigned> domainSorts;
  static Stack<TermList> predArgs;
  domainSorts.reset();
  predArgs.reset();

  ensureHavingVarSorts();

  List<unsigned>::Iterator vit(free);
  while (vit.hasNext()) {
    unsigned uvar = vit.next();
    domainSorts.push(_varSorts.get(uvar, Sorts::SRT_DEFAULT));
    predArgs.push(TermList(uvar, false));
  }

  predSym->setType(new PredicateType(length, domainSorts.begin()));

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

  List<unsigned>* fv = List<unsigned>::empty();
  List<unsigned>::pushFromIterator(VarSet::Iterator(*freeVars(g)), fv);

  Literal* naming = createNamingLiteral(g, fv);
  Formula* name = new AtomicFormula(naming);

  occurrences.replaceBy(name);

  enqueue(g);

  for (SIGN sign : { NEGATIVE, POSITIVE }) {
    // One could also consider the case where (part of) the bindings goes to the definition
    // which perhaps allows us to the have a skolem predicate with fewer arguments
    introduceGenClause(GenLit(name, OPPOSITE(sign)), GenLit(g, sign));
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
      process(g->getBooleanTerm(), occurrences);
      break;

    case LITERAL:
      process(g->literal(),occurrences);
      break;

    case NOT:
      ASS_REP(g->uarg()->connective() == BOOL_TERM, g->uarg()->toString());
      ASS_REP(g->uarg()->getBooleanTerm().isVar(),  g->uarg()->toString());
      processBoolVar(NEGATIVE, g->uarg()->getBooleanTerm().var(), occurrences);
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

  BindingList::Iterator bit(gc->bindings);
  while (bit.hasNext()) {
    Binding b = bit.next();
    unsigned var = b.first;
    Term* skolem = b.second;
    if (skolem->isSpecial()) {
      variables.push(var);
      ASS(skolem->isFormula());
      Formula* f = skolem->getSpecialData()->getFormula();
      ASS(f->connective() == LITERAL);
      skolems.push(f);
    }
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

    while (List<List<GenLit>*>::isNonEmpty(genClauses)) {
      List<GenLit>* gls = List<List<GenLit>*>::pop(genClauses);

      bool occurs = false;
      // We might have a predicate skolem binding for a variable that does not
      // occur in the generalised clause.
      // TODO: optimize?
      List<GenLit>::Iterator glsit(gls);
      while (glsit.hasNext()) {
        GenLit gl = glsit.next();
        if (formula(gl)->freeVariables()->member(variable)) {
          occurs = true;
          break;
        }
      }

      if (!occurs) {
        processedGenClauses = processedGenClauses->cons(gls);
        continue;
      }

      List<GenLit>* thenGls(0);
      if (mapSubstitution(gls, thenSubst, thenGls)) {
        processedGenClauses = processedGenClauses->cons(thenGls->cons(GenLit(skolem, NEGATIVE)));
      }

      List<GenLit>* elseGls(0);
      if (mapSubstitution(gls, elseSubst, elseGls)) {
        processedGenClauses = processedGenClauses->cons(elseGls->cons(GenLit(skolem, POSITIVE)));
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
    SPGenClause genClause = makeGenClause(gls, gc->bindings);
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

bool NewCNF::mapSubstitution(List<GenLit>* clause, Substitution subst, List<GenLit>* output)
{
  CALL("NewCNF::mapSubstitution");

  List<GenLit>::Iterator it(clause);
  while (it.hasNext()) {
    GenLit gl = it.next();
    Formula* f = SubstHelper::apply(formula(gl), subst);
    ASS_NEQ(f, formula(gl));

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
        output = output->cons(GenLit(f, sign(gl)));
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

  static Substitution subst;
  ASS(subst.isEmpty());

  BindingList::Iterator bit(gc->bindings);
  while (bit.hasNext()) {
    Binding b = bit.next();
    subst.bind(b.first, b.second);
  }

  // TODO: since the bindings are share, there is no easy way to delete them

  static Stack<Literal*> properLiterals;
  ASS(properLiterals.isEmpty());

  GenClause::Iterator lit = gc->genLiterals();
  while (lit.hasNext()) {
    GenLit gl = lit.next();
    Formula* g = formula(gl);

    ASS_REP(g->connective() == LITERAL, gc->toString());
    ASS_REP(g->literal()->shared(), g->toString());
    ASS_REP((SIGN)g->literal()->polarity() == POSITIVE, g->toString());

    Literal* l = g->literal()->apply(subst);
    if (sign(gl) == NEGATIVE) {
      l = Literal::complementaryLiteral(l);
    }

    properLiterals.push(l);
  }

  Inference* inference = new Inference1(Inference::CLAUSIFY, _beingClausified);
  Clause* clause = new(gc->size()) Clause(gc->size(), _beingClausified->inputType(), inference);
  for (int i = gc->size() - 1; i >= 0; i--) {
    (*clause)[i] = properLiterals[i];
  }

  properLiterals.reset();
  subst.reset();

  return clause;
}

}
