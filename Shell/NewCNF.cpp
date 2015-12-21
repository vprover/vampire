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
#include "Shell/Skolem.hpp"
#include "NewCNF.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Signature.hpp"
#include "SymbolOccurrenceReplacement.hpp"

using namespace Lib;
using namespace Kernel;

namespace Shell {

#undef LOGGING
#define LOGGING 0

#if LOGGING
#define LOG1(arg) cout << arg << endl;
#define LOG2(a1,a2) cout << a1 << a2 << endl;
#define LOG3(a1,a2,a3) cout << a1 << a2 << a3 << endl;
#else
#define LOG1(arg)
#define LOG2(a1,a2)
#define LOG3(a1,a2,a3)
#endif

void NewCNF::clausify(FormulaUnit* unit,Stack<Clause*>& output)
{
  CALL("NewCNF::clausify");

  _beingClausified = unit;

  Formula* f = unit->formula();

  LOG2("clausify ",f->toString());

  switch (f->connective()) {
  case TRUE:
    return;
  case FALSE:
    {
      // create an empty clause and push it in the stack
      Inference* inf = new Inference1(Inference::CLAUSIFY,unit);
      Clause* clause = new(0) Clause(0, unit->inputType(),inf);
      output.push(clause);
    }
    return;
  default:
    break;
  }

  ASS(_genClauses.empty());
  ASS(_queue.isEmpty());
  ASS(_occurrences.isEmpty());

  enqueue(f);

  SPGenClause topLevel = introduceGenClause(1, BindingList::empty());
  setLiteral(topLevel, 0, GenLit(f, POSITIVE));

  process();

  for (SPGenClause gc : _genClauses) {
    output.push(toClause(gc));
  }

  _genClauses.clear();
  _varSorts.reset();
  _freeVars.reset();

  ASS(_queue.isEmpty());
  ASS(_occurrences.isEmpty());
}

void NewCNF::process(Literal* literal, Occurrences &occurrences) {
  CALL("NewCNF::process(Literal*)");

  LOG2("process(Literal*) ", literal->toString());
  LOG2("occurrences.size ", occurrences.size());

  ASS_REP(!literal->shared(), literal->toString());

  if (literal->isEquality()) {
    TermList argument[2];
    bool isFormula[2];

    for (SIDE side : { LEFT, RIGHT }) {
      argument[side]  = *literal->nthArgument(side);
      isFormula[side] = argument[side].isTerm() && argument[side].term()->isBoolean();
    }

    if (isFormula[LEFT] || isFormula[RIGHT]) {
      Formula* processedformula[2];
      for (SIDE side : { LEFT, RIGHT }) {
        if (isFormula[side]) {
          if (argument[side].term()->isFormula()) {
            processedformula[side] = argument[side].term()->getSpecialData()->getFormula();
          } else {
            processedformula[side] = new BoolTermFormula(argument[side]);
          }
        } else {
          ASS(argument[side].isVar());
          Literal* eqLiteral = Literal::createEquality(POSITIVE, argument[side], TermList(Term::foolTrue()), Sorts::SRT_BOOL);
          processedformula[side] = new AtomicFormula(eqLiteral);
        }
      }

      Formula* equivalence = new BinaryFormula(IFF, processedformula[LEFT], processedformula[RIGHT]);

      enqueue(equivalence);

      Occurrences::Iterator occit(occurrences);
      while (occit.hasNext()) {
        Occurrence occ = occit.next();
        formula(occ.gc->literals[occ.position]) = equivalence;
      }
    }
  }

  Stack<Term*> specialTerms;
  Stack<TermList> names;

  Stack<TermList> arguments;
  Term::Iterator lit(literal);
  while (lit.hasNext()) {
    arguments.push(findSpecialTermData(lit.next(), specialTerms, names));
  }

  Formula* processedLiteral = new AtomicFormula(Literal::create(literal, arguments.begin()));

  Occurrences::Iterator occit(occurrences);
  while (occit.hasNext()) {
    Occurrence occ = occit.next();
    formula(occ.gc->literals[occ.position]) = processedLiteral;
  }

  while (specialTerms.isNonEmpty()) {
    Term* term = specialTerms.pop();
    ASS_REP(term->isSpecial(), term->toString());

    TermList name = names.pop();

    Term::SpecialTermData* sd = term->getSpecialData();
    switch (sd->getType()) {
      case Term::SF_FORMULA: {
        Formula* f = sd->getFormula();

        enqueue(f);

        for (SIGN sign : { POSITIVE, NEGATIVE }) {
          SPGenClause gc = introduceGenClause(2);
          setLiteral(gc, 0, GenLit(f, sign));
          static TermList true_(Term::foolTrue());
          Literal* namingLiteral = Literal::createEquality(OPPOSITE(sign), true_, name, Sorts::SRT_BOOL);
          Formula* naming = new AtomicFormula(namingLiteral);
          setLiteral(gc, 1, GenLit(naming, POSITIVE));
        }
        break;
      }

      case Term::SF_ITE: {
        Formula* condition  = sd->getCondition();
        TermList thenBranch = *term->nthArgument(0);
        TermList elseBranch = *term->nthArgument(1);

        enqueue(condition);

        for (SIGN sign : { POSITIVE, NEGATIVE }) {
          SPGenClause gc = introduceGenClause(2);
          setLiteral(gc, 0, GenLit(condition, sign));
          TermList branch = sign == NEGATIVE ? thenBranch : elseBranch;
          Literal* namingLiteral = Literal::createEquality(POSITIVE, name, branch, sd->getSort());
          Formula* naming = new AtomicFormula(namingLiteral);
          setLiteral(gc, 1, GenLit(naming, POSITIVE));
        }
        break;
      }

      case Term::SF_LET:
        NOT_IMPLEMENTED;

      default:
        ASSERTION_VIOLATION;
    }
  }
}

TermList NewCNF::findSpecialTermData(TermList ts, Stack<Term*> &specialTerms, Stack<TermList> &names)
{
  CALL("NewCNF::findSpecialTermData");

  if (ts.isVar() || ts.term()->shared()) {
    return ts;
  } else {
    Term* term = ts.term();
    if (term->isSpecial()) {
      specialTerms.push(term);

      IntList* freeVars = term->freeVariables();

      static Stack<unsigned> sorts;
      sorts.reset();

      ensureHavingVarSorts();

      IntList::Iterator vit(freeVars);
      while (vit.hasNext()) {
        unsigned var = (unsigned) vit.next();
        sorts.push(_varSorts.get(var, Sorts::SRT_DEFAULT));
      }

      unsigned arity = (unsigned) freeVars->length();
      FunctionType* type = new FunctionType(arity, sorts.begin(), Sorts::SRT_BOOL);

      unsigned freshFunctor = env.signature->addFreshFunction(arity, "bG");
      env.signature->getFunction(freshFunctor)->setType(type);

      const TermList name = createNamingTerm(freshFunctor, freeVars);
      names.push(name);

      return name;
    } else {
      Stack<TermList> arguments;

      Term::Iterator it(term);
      while (it.hasNext()) {
        arguments.push(findSpecialTermData(it.next(), specialTerms, names));
      }

      return TermList(Term::create(term, arguments.begin()));
    }
  }
}

void NewCNF::process(JunctionFormula *g, Occurrences &occurrences)
{
  CALL("NewCNF::process(JunctionFormula*)");

  LOG2("processJunction ",g->toString());
  LOG2("occurrences.size ", occurrences.size());

  FormulaList::Iterator ait(g->args());
  while (ait.hasNext()) {
    enqueue(ait.next());
  }

  SIGN formulaSign = g->connective() == OR ? POSITIVE : NEGATIVE;

  while (occurrences.isNonEmpty()) {
    Occurrence occ = pop(occurrences);

    if (occ.sign() == formulaSign) {
      SPGenClause processedGc = introduceGenClause(occ.gc->size() + g->args()->length() - 1, occ.gc->bindings);
      for (unsigned i = 0, position = 0; i < occ.gc->size(); i++) {
        if (i == occ.position) {
          ASS_EQ(formula(occ.gc->literals[i]), g);
          FormulaList::Iterator it(g->args());
          while (it.hasNext()) {
            setLiteral(processedGc, position++, GenLit(it.next(), occ.sign()));
          }
        } else {
          setLiteral(processedGc, position++, occ.gc->literals[i]);
        }
      }
    } else {
      FormulaList::Iterator it(g->args());
      while (it.hasNext()) {
        Formula* arg = it.next();
        SPGenClause processedGc = introduceGenClause(occ.gc->size(), occ.gc->bindings);
        for (unsigned i = 0; i < occ.gc->size(); i++) {
          if (i == occ.position) {
            ASS_EQ(formula(occ.gc->literals[i]), g);
            setLiteral(processedGc, i, GenLit(arg, occ.sign()));
          } else {
            setLiteral(processedGc, i, occ.gc->literals[i]);
          }
        }
      }
    }
  }
}

void NewCNF::process(BinaryFormula* g, Occurrences &occurrences)
{
  CALL("NewCNF::process(BinaryFormula*)");

  LOG2("processEquivalence ",g->toString());

  ASS(g->connective() != IMP);

  enqueue(g->left());
  enqueue(g->right());

  SIGN formulaSign = g->connective() == IFF ? POSITIVE : NEGATIVE;

  while (occurrences.isNonEmpty()) {
    Occurrence occ = pop(occurrences);

    for (SIGN lhsSign : { NEGATIVE, POSITIVE }) {
      SPGenClause processedGc = introduceGenClause(occ.gc->size() + 1, occ.gc->bindings);
      for (unsigned i = 0, position = 0; i < occ.gc->size(); i++) {
        if (i == occ.position) {
          ASS_EQ(formula(occ.gc->literals[i]), g);
          SIGN rhsSign = formulaSign == occ.sign() ? OPPOSITE(lhsSign) : lhsSign;
          setLiteral(processedGc, position++, GenLit(g->left(),  lhsSign));
          setLiteral(processedGc, position++, GenLit(g->right(), rhsSign));
        } else {
          setLiteral(processedGc, position++, occ.gc->literals[i]);
        }
      }
    }
  }
}

void NewCNF::processBoolVar(TermList var, Occurrences &occurrences)
{
  CALL("NewCNF::processBoolVar");

  Literal* processedLiteral = Literal::createEquality(POSITIVE, var, TermList(Term::foolTrue()), Sorts::SRT_BOOL);
  Formula* processedFormula = new AtomicFormula(processedLiteral);

  Occurrences::Iterator occit(occurrences);
  while (occit.hasNext()) {
    Occurrence occ = occit.next();
    GenLit& gl = occ.gc->literals[occ.position];
    formula(gl) = processedFormula;
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
      SPGenClause processedGc = introduceGenClause(occ.gc->size() + 1, occ.gc->bindings);
      for (unsigned i = 0, position = 0; i < occ.gc->size(); i++) {
        if (i == occ.position) {
          Formula* branch = conditionSign == NEGATIVE ? thenBranch : elseBranch;
          setLiteral(processedGc, position++, GenLit(condition, conditionSign));
          setLiteral(processedGc, position++, GenLit(branch, occ.sign()));
        } else {
          setLiteral(processedGc, position++, occ.gc->literals[i]);
        }
      }
    }
  }
}

void NewCNF::processLet(unsigned symbol, Formula::VarList*bindingVariables, TermList binding, Formula* contents, Occurrences &occurrences)
{
  CALL("NewCNF::processLet");

  bool isPredicate = binding.isTerm() && binding.term()->isBoolean();

  Formula::VarList* bindingFreeVars(0);
  Formula::VarList::Iterator bfvi(binding.freeVariables());
  while (bfvi.hasNext()) {
    int var = bfvi.next();
    if (!bindingVariables->member(var)) {
      bindingFreeVars = new Formula::VarList(var, bindingFreeVars);
    }
  }

  unsigned nameArity = (unsigned) bindingVariables->length() + bindingFreeVars->length();
  unsigned nameSort;
  if (!isPredicate) {
    nameSort = env.signature->getFunction(symbol)->fnType()->result();
  }

  Formula* processedContents;
  unsigned freshSymbol;

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
      freshSymbol = env.signature->addFreshFunction(nameArity, "lG");
      env.signature->getPredicate(freshSymbol)->setType(type);
    } else {
      FunctionType* type = new FunctionType(nameArity, sorts.begin(), nameSort);
      freshSymbol = env.signature->addFreshFunction(nameArity, "lG");
      env.signature->getFunction(freshSymbol)->setType(type);
    }

    SymbolOccurrenceReplacement replacement(isPredicate, symbol, freshSymbol, bindingFreeVars);
    processedContents = replacement.process(contents);
  } else {
    freshSymbol = symbol;
    processedContents = contents;
  }

  enqueue(processedContents);

  Occurrences::Iterator occit(occurrences);
  while (occit.hasNext()) {
    Occurrence occ = occit.next();
    GenLit& gl = occ.gc->literals[occ.position];
    formula(gl) = processedContents;
  }

  Formula::VarList* variables = bindingFreeVars->append(bindingVariables);

  Stack<TermList> arguments;
  Formula::VarList::Iterator vit(variables);
  while (vit.hasNext()) {
    unsigned var = (unsigned)vit.next();
    arguments.push(TermList(var, false));
  }

  if (isPredicate) {
    Formula* formulaBinding = new BoolTermFormula(binding);

    enqueue(formulaBinding);

    Literal* name = Literal::create(freshSymbol, nameArity, POSITIVE, false, arguments.begin());
    Formula* nameFormula = new AtomicFormula(name);

    for (SIGN sign : { POSITIVE, NEGATIVE }) {
      SPGenClause gc = introduceGenClause(2);
      setLiteral(gc, 0, GenLit(nameFormula, sign));
      setLiteral(gc, 1, GenLit(formulaBinding, POSITIVE));
    }
  } else {
    TermList name = TermList(Term::create(freshSymbol, nameArity, arguments.begin()));
    Formula* nameFormula = new AtomicFormula(Literal::createEquality(POSITIVE, name, binding, nameSort));
    SPGenClause gc = introduceGenClause(1);
    setLiteral(gc, 0, GenLit(nameFormula, POSITIVE));
  }
}

NewCNF::VarSet* NewCNF::freeVars(Formula* g)
{
  CALL("NewCNF::freeVars");

  // LOG2("freeVars for ",g->toString());

  VarSet* res;

  if (!_freeVars.find(g,res)) {
    switch (g->connective()) {
      case LITERAL: {
        VariableIterator vit(g->literal());
        static Stack<unsigned> is;
        is.reset();
        while (vit.hasNext()) {
          is.push(vit.next().var());
        }
        res = (VarSet*) VarSet::getFromArray(is.begin(),is.size());
        break;
      }
      case AND:
      case OR: {
        FormulaList::Iterator aIt(g->args());
        ASS(aIt.hasNext());
        res = freeVars(aIt.next());
        while (aIt.hasNext()) {
          res = (VarSet*) res->getUnion(freeVars(aIt.next()));
        }
        break;
      }
      case IFF:
      case XOR: {
        res = freeVars(g->left());
        res = (VarSet*) res->getUnion(freeVars(g->right()));
        break;
      }
      case FORALL:
      case EXISTS: {
        res = freeVars(g->qarg());
        Formula::VarList::Iterator vit(g->vars());
        res = (VarSet*) res->subtract(VarSet::getFromIterator(vit));
        break;
      }
      default:
        ASSERTION_VIOLATION;
    }
    _freeVars.insert(g,res);
  }

  return res;
}

void NewCNF::ensureHavingVarSorts()
{
  CALL("NewCNF::ensureHavingVarSorts");

  if (_varSorts.size() == 0) {
    SortHelper::collectVariableSorts(_beingClausified->formula(), _varSorts);
  }
}

Kernel::Term* NewCNF::createSkolemTerm(unsigned var, VarSet* free)
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

  unsigned fun = Skolem::addSkolemFunction(arity, domainSorts.begin(), rangeSort, var);

  Term* res = Term::create(fun, arity, fnArgs.begin());

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
    VarSet* boundVars = (VarSet*) VarSet::getFromIterator(getMappingIterator(bIt, BindingGetFirstFunctor()));
    VarSet* unboundFreeVars = (VarSet*) freeVars(g)->subtract(boundVars);

    if (!_skolemsByFreeVars.find(unboundFreeVars, processedBindings)) {
      // second level cache miss, let's do the actual skolemisation

      processedBindings = nullptr;

      Formula::VarList::Iterator vs(g->vars());
      while (vs.hasNext()) {
        unsigned var = (unsigned)vs.next();
        Term* skolemTerm = createSkolemTerm(var, unboundFreeVars);
        BindingList::push(make_pair(var,skolemTerm), processedBindings);
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

  LOG2("NewCNF::process(QuantifiedFormula*) ", g->toString());

  // Note that the formula under quantifier reuses the quantified formula's occurrences
  enqueue(g->qarg(), occurrences);

  // the skolem caches are empty
  ASS(_skolemsByBindings.isEmpty());
  ASS(_skolemsByFreeVars.isEmpty());

  // Correct all the GenClauses to mention qarg instead of g
  //
  // In the skolemising polarity introduce new skolems as you go
  // each occurrence may need a new set depending on bindings,
  // but let's try to share as much as possible
  Occurrences::Iterator occit(occurrences);
  while (occit.hasNext()) {
    Occurrence occ = occit.next();

    GenLit& gl = occ.gc->literals[occ.position];
    ASS_EQ(formula(gl),g);
    formula(gl) = g->qarg();

    if ((occ.sign() == POSITIVE) == (g->connective() == EXISTS)) {
      skolemise(g, occ.gc->bindings);
    }
  }

  // empty the skolem caches
  _skolemsByBindings.reset();
  Lib::DHMap<VarSet*,BindingList*>::DelIterator dIt(_skolemsByFreeVars);
  while (dIt.hasNext()) {
    VarSet* vars;
    BindingList* bindings;
    dIt.next(vars,bindings);
    bindings->destroy();
    dIt.del();
  }
}

/**
 * Stolen from Naming::getDefinitionLiteral
 */
Literal* NewCNF::createNamingLiteral(Formula* f, VarSet* free)
{
  CALL("NewCNF::createNamingLiteral");

  unsigned length = free->size();
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

  VarSet::Iterator vit(*free);
  while (vit.hasNext()) {
    unsigned uvar = vit.next();
    domainSorts.push(_varSorts.get(uvar, Sorts::SRT_DEFAULT));
    predArgs.push(TermList(uvar, false));
  }

  predSym->setType(new PredicateType(length, domainSorts.begin()));

  return Literal::create(pred, length, true, false, predArgs.begin());
}

TermList NewCNF::createNamingTerm(unsigned functor, IntList* vars)
{
  CALL("NewCNF::createNamingTerm");
  unsigned arity = (unsigned)vars->length();

  Stack<TermList> arguments;
  Formula::VarList::Iterator vit(vars);
  while (vit.hasNext()) {
    unsigned var = (unsigned)vit.next();
    arguments.push(TermList(var, false));
  }

  return TermList(Term::create(functor, arity, arguments.begin()));
}

/**
 * Formula g with occurrences is being named.
 * Introduce a new symbol skP, replace the occurrences by skP(U,V,..)
 * where U,V,.. are free variables of g and
 * and return skP(U,V,..).
 *
 * Occurrence lists in occurrences get destroyed.
 */
Formula* NewCNF::nameSubformula(Kernel::Formula* g, Occurrences &occurrences)
{
  CALL("NewCNF::nameSubformula");

  LOG2("performedNaming for ",g->toString());
  for (SPGenClause gc : _genClauses) {
    LOG1(gc->toString());
  }

  ASS_NEQ(g->connective(), LITERAL);
  ASS_NEQ(g->connective(), NOT);

  Formula* name = new AtomicFormula(createNamingLiteral(g, freeVars(g)));

  for (SIGN sign : { NEGATIVE, POSITIVE }) {
    // One could also consider the case where (part of) the bindings goes to the definition
    // which perhaps allows us to the have a skolem predicate with fewer arguments
    SPGenClause gc = introduceGenClause(2, BindingList::empty());
    setLiteral(gc, 0, GenLit(name, OPPOSITE(sign)));
    setLiteral(gc, 1, GenLit(g, sign));
  }

  Occurrences::Iterator occit(occurrences);
  while (occit.hasNext()) {
    Occurrence occ = occit.next();
    GenLit& gl = occ.gc->literals[occ.position];
    ASS_EQ(formula(gl),g);
    formula(gl) = name;
  }

  return name;
}

void NewCNF::process()
{
  CALL("NewCNF::process()");

  // process the generalized clauses until they contain only literals
  while(_queue.isNonEmpty()) {
    Formula* g;
    Occurrences occurrences;
    dequeue(g, occurrences);

    LOG1("process() iteration; _genClauses:");
    for (SPGenClause gc : _genClauses) {
      LOG1(gc->toString());
    }

    if (g->connective() != LITERAL) {
      if ((_namingThreshold > 1) && occurrences.size() > _namingThreshold) {
        nameSubformula(g, occurrences);
      }
    }

    // TODO: currently we don't check for tautologies, as there should be none appearing (we use polarity based expansion of IFF and XOR)

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

      case BOOL_TERM: {
        TermList ts = g->getBooleanTerm();
        if (ts.isVar()) {
          processBoolVar(ts, occurrences);
          break;
        }

        Term* term = ts.term();
        ASS_REP(term->isSpecial(), term->toString());

        Term::SpecialTermData* sd = term->getSpecialData();
        switch (sd->getType()) {
          case Term::SF_ITE: {
            Formula* condition = sd->getCondition();

            Formula* branch[2];
            for (SIDE side : { LEFT, RIGHT }) {
              TermList branchTerm = *term->nthArgument(side);
              ASS_REP(branchTerm.isVar() || (branchTerm.term()->isSpecial() && branchTerm.term()->isFormula()),
                      branchTerm.toString());
              branch[side] = branchTerm.isVar() ? (Formula*) new BoolTermFormula(branchTerm)
                                                : branchTerm.term()->getSpecialData()->getFormula();
            }

            processITE(condition, branch[LEFT], branch[RIGHT], occurrences);
            break;
          }

          case Term::SF_LET: {
            unsigned functor = sd->getFunctor();
            Formula::VarList* variables = sd->getVariables();
            TermList binding = sd->getBinding();
            Formula* contents = new BoolTermFormula(*term->nthArgument(0));

            processLet(functor, variables, binding, contents, occurrences);
            break;
          }

          default:
            ASSERTION_VIOLATION_REP(term->toString());
        }
        break;
      }

      case LITERAL:
        process(g->literal(),occurrences);
        break;

      default:
        ASSERTION_VIOLATION_REP(g->toString());
    }
  }
}

Clause* NewCNF::toClause(SPGenClause gc)
{
  CALL("NewCNF::toClause");

  static Substitution subst;
  ASS(subst.isEmpty());

  BindingList::Iterator bIt(gc->bindings);
  while (bIt.hasNext()) {
    Binding b = bIt.next();
    subst.bind(b.first,b.second);
  }

  // TODO: since the bindings are share, there is no easy way to delete them

  static Stack<Literal*> properLiterals;
  ASS(properLiterals.isEmpty());

  unsigned len = gc->size();
  for (unsigned i = 0; i < len; i++) {
    Formula* g = formula(gc->literals[i]);

    ASS_REP(g->connective() == LITERAL, g->toString());

    Literal* l = g->literal()->apply(subst);
    if (sign(gc->literals[i]) == NEGATIVE) {
      l = Literal::complementaryLiteral(l);
    }

    properLiterals.push(l);
  }

  Inference* inference = new Inference1(Inference::CLAUSIFY, _beingClausified);
  Clause* clause = new(len) Clause(len, _beingClausified->inputType(), inference);
  for (int i = len-1;i >= 0;i--) {
    (*clause)[i] = properLiterals[i];
  }

  properLiterals.reset();
  subst.reset();

  return clause;
}

}
