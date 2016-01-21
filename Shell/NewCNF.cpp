/**
 * @file NewCNF.cpp
 * Implements class NewCNF implementing the new CNF transformation.
 * @since 19/11/2015 Manchester
 */

#include <Kernel/SubstHelper.hpp>
#include "Debug/Tracer.hpp"

#include "Kernel/Sorts.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/SortHelper.hpp"
#include "Shell/Skolem.hpp"
#include "Shell/Options.hpp"
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

    for (SPGenClause gc : _genClauses) {
      LOG1(gc->toString());
    }

    if (g->connective() != LITERAL) {
      if ((_namingThreshold > 1) && occurrences.size() > _namingThreshold) {
        nameSubformula(g, occurrences);
      }
    }

    // TODO: currently we don't check for tautologies, as there should be none appearing (we use polarity based expansion of IFF and XOR)
    process(g, occurrences);
  }

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

//  ASS_REP(!literal->shared(), literal->toString());
  if (literal->shared()) {
    return;
  }

  if (literal->isEquality()) {
    TermList argument[2];
    bool isFormula[2];

    for (SIDE side : { LEFT, RIGHT }) {
      argument[side]  = *literal->nthArgument(side);
      isFormula[side] = argument[side].isTerm() && argument[side].term()->isBoolean();
    }

    if (isFormula[LEFT] || isFormula[RIGHT]) {
      Formula* processedFormula[2];
      for (SIDE side : { LEFT, RIGHT }) {
        if (isFormula[side]) {
          processedFormula[side] = BoolTermFormula::create(argument[side]);
        } else {
          ASS_REP(argument[side].isVar(), argument[side].toString());
          Literal* eqLiteral = Literal::createEquality(POSITIVE, argument[side], TermList(Term::foolTrue()), Sorts::SRT_BOOL);
          processedFormula[side] = new AtomicFormula(eqLiteral);
        }
      }

      Formula* equivalence = new BinaryFormula(IFF, processedFormula[LEFT], processedFormula[RIGHT]);

      occurrences.replaceBy(equivalence);

      enqueue(equivalence, occurrences);

      return;
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

  occurrences.replaceBy(processedLiteral);

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
          Literal* namingLiteral = Literal::createEquality(OPPOSITE(sign), TermList(Term::foolTrue()), name, Sorts::SRT_BOOL);
          Formula* naming = new AtomicFormula(namingLiteral);
          introduceGenClause(GenLit(f, sign), GenLit(naming, POSITIVE));
        }
        break;
      }

      case Term::SF_ITE: {
        Formula* condition  = sd->getCondition();
        TermList thenBranch = *term->nthArgument(0);
        TermList elseBranch = *term->nthArgument(1);

        enqueue(condition);

        for (SIGN sign : { POSITIVE, NEGATIVE }) {
          TermList branch = sign == NEGATIVE ? thenBranch : elseBranch;
          Literal* namingLiteral = Literal::createEquality(POSITIVE, name, branch, sd->getSort());
          Formula* naming = new AtomicFormula(namingLiteral);
          introduceGenClause(GenLit(condition, sign), GenLit(naming, POSITIVE));
        }
        break;
      }

      case Term::SF_LET: {
//        unsigned symbol = sd->getFunctor();
//        Formula::VarList* variables = sd->getVariables();
//        TermList binding = sd->getBinding();
//        TermList contents = *term->nthArgument(0);

        NOT_IMPLEMENTED;
        break;
      }

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
  }

  Term* term = ts.term();
  if (!term->isSpecial()) {
    Stack<TermList> arguments;

    Term::Iterator it(term);
    while (it.hasNext()) {
      arguments.push(findSpecialTermData(it.next(), specialTerms, names));
    }

    return TermList(Term::create(term, arguments.begin()));
  }

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

  unsigned resultSort = term->isFormula() ? Sorts::SRT_BOOL : term->getSpecialData()->getSort();

  unsigned arity = (unsigned) freeVars->length();
  FunctionType* type = new FunctionType(arity, sorts.begin(), resultSort);

  unsigned freshFunctor = env.signature->addFreshFunction(arity, "bG");
  env.signature->getFunction(freshFunctor)->setType(type);

  const TermList name = createNamingTerm(freshFunctor, freeVars);
  names.push(name);

  return name;
}

void NewCNF::process(JunctionFormula *g, Occurrences &occurrences)
{
  CALL("NewCNF::process(JunctionFormula*)");

  LOG2("processJunction ",g->toString());
  LOG2("occurrences.size ", occurrences.size());

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

  LOG2("processBinary ", g->toString());
  LOG2("occurrences.size ", occurrences.size());

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

void NewCNF::processBoolVar(unsigned var, Occurrences &occurrences)
{
  CALL("NewCNF::processBoolVar");

  /**
   * Note the following two facts:
   * 1) ![X:$o]:(X | f) <=> (1 | f) & (0 | f) <=> 1 & f <=> f
   * 2) ?[X:$o]:(X | f) <=> (1 | f) | (0 | f) <=> 1 | f <=> 1
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

    BindingList::Iterator bit(occ.gc->bindings);
    VarSet* boundVars = (VarSet*) VarSet::getFromIterator(getMappingIterator(bit, BindingGetVarFunctor()));

    if (boundVars->member(var)) {
      continue;
    }

    removeGenLit(occ.gc, occ.position);
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

  TermList processedContents;
  if (binding.isVar() || !binding.term()->isSpecial()) {
    processedContents = inlineLetBinding(symbol, bindingVariables, binding, contents);
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] clausify (inline let) in:  " << contents.toString() << std::endl;
      env.out() << "[PP] clausify (inline let) out: " << processedContents.toString() << std::endl;
      env.endOutput();
    }
  } else {
    processedContents = nameLetBinding(symbol, bindingVariables, binding, contents);
    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] clausify (name let) binding: " << binding.toString() << std::endl;
      env.out() << "[PP] clausify (name let) in:  " << contents.toString() << std::endl;
      env.out() << "[PP] clausify (name let) out: " << processedContents.toString() << std::endl;
      env.endOutput();
    }
  }

  Formula* processedContentsFormula = BoolTermFormula::create(processedContents);

  occurrences.replaceBy(processedContentsFormula);

  process(processedContentsFormula, occurrences);
}

TermList NewCNF::nameLetBinding(unsigned symbol, Formula::VarList *bindingVariables, TermList binding, TermList contents)
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
      introduceGenClause(GenLit(nameFormula, sign), GenLit(formulaBinding, POSITIVE));
    }
  } else {
    TermList name = TermList(Term::create(freshSymbol, nameArity, arguments.begin()));
    Formula* nameFormula = new AtomicFormula(Literal::createEquality(POSITIVE, name, binding, nameSort));
    introduceGenClause(GenLit(nameFormula, POSITIVE));
  }

  if (renameSymbol) {
    SymbolOccurrenceReplacement replacement(isPredicate, symbol, freshSymbol, bindingFreeVars);
    return replacement.process(contents);
  }

  return contents;
}

TermList NewCNF::inlineLetBinding(unsigned symbol, Formula::VarList *bindingVariables, TermList binding, TermList contents) {
  CALL("NewCNF::inlineLetBinding(TermList)");

  bool isPredicate = binding.isTerm() && binding.term()->isBoolean();

  if (contents.isVar()) {
    return contents;
  }

  Term* term = contents.term();

  if (term->isSpecial()) {
    Term::SpecialTermData *sd = term->getSpecialData();
    switch (sd->getType()) {
      case Term::SF_FORMULA:
        return TermList(Term::createFormula(inlineLetBinding(symbol, bindingVariables, binding, sd->getFormula())));

      case Term::SF_ITE:
        return TermList(Term::createITE(sd->getCondition(),
                                        inlineLetBinding(symbol, bindingVariables, binding, *term->nthArgument(0)),
                                        inlineLetBinding(symbol, bindingVariables, binding, *term->nthArgument(1)),
                                        sd->getSort()));

      case Term::SF_LET:
        return TermList(Term::createLet(sd->getFunctor(), sd->getVariables(),
                                        inlineLetBinding(symbol, bindingVariables, binding, sd->getBinding()),
                                        inlineLetBinding(symbol, bindingVariables, binding, *term->nthArgument(0)),
                                        sd->getSort()));

      default:
        NOT_IMPLEMENTED;
    }
  }

  Term::Iterator it(term);

  if (!isPredicate && (term->functor() == symbol)) {
    Substitution subst;

    Formula::VarList::Iterator vit(bindingVariables);
    while (it.hasNext() && vit.hasNext()) {
      unsigned var = (unsigned) vit.next();
      TermList arg = it.next();
      subst.bind(var, arg);
    }

    return SubstHelper::apply(binding, subst);
  } else {
    Stack<TermList> arguments;
    while (it.hasNext()) {
      arguments.push(inlineLetBinding(symbol, bindingVariables, binding, it.next()));
    }

    return TermList(Term::create(term, arguments.begin()));
  }
}

Formula* NewCNF::inlineLetBinding(unsigned symbol, Formula::VarList *bindingVariables, TermList binding, Formula* contents) {
  CALL("NewCNF::inlineLetBinding(Formula*)");

  bool isPredicate = binding.isTerm() && binding.term()->isBoolean();

  switch (contents->connective()) {
    case LITERAL: {
      Literal* literal = contents->literal();
      Term::Iterator it(literal);

      if (isPredicate && (literal->functor() == symbol)) {
        Substitution subst;

        Formula::VarList::Iterator vit(bindingVariables);
        while (it.hasNext() && vit.hasNext()) {
          unsigned var = (unsigned) vit.next();
          TermList arg = it.next();
          subst.bind(var, arg);
        }

        return BoolTermFormula::create(SubstHelper::apply(binding, subst));
      } else {
        Stack<TermList> arguments;
        while (it.hasNext()) {
          arguments.push(inlineLetBinding(symbol, bindingVariables, binding, it.next()));
        }

        return new AtomicFormula(Literal::create(literal, arguments.begin()));
      }
    }

    case AND:
    case OR: {
      FormulaList* args(0);

      FormulaList::Iterator ait(contents->args());
      while (ait.hasNext()) {
        args = new FormulaList(inlineLetBinding(symbol, bindingVariables, binding, ait.next()), args);
      }

      // TODO: do this faster
      return new JunctionFormula(contents->connective(), args->reverse());
    }

    case IFF:
    case XOR:
      return new BinaryFormula(contents->connective(),
                               inlineLetBinding(symbol, bindingVariables, binding, contents->left()),
                               inlineLetBinding(symbol, bindingVariables, binding, contents->right()));

    case FORALL:
    case EXISTS:
      return new QuantifiedFormula(contents->connective(), contents->vars(), contents->sorts(),
                                   inlineLetBinding(symbol, bindingVariables, binding, contents->qarg()));

    case BOOL_TERM:
      return new BoolTermFormula(inlineLetBinding(symbol, bindingVariables, binding, contents->getBooleanTerm()));

    default:
      ASSERTION_VIOLATION_REP(contents->toString());
  }
}

NewCNF::VarSet* NewCNF::freeVars(Formula* g)
{
  CALL("NewCNF::freeVars");

  LOG2("freeVars for ", g->toString());

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
    VarSet* boundVars = (VarSet*) VarSet::getFromIterator(getMappingIterator(bIt, BindingGetVarFunctor()));
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

  // Correct all the GenClauses to mention qarg instead of g
  occurrences.replaceBy(g->qarg());

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
  Lib::DHMap<VarSet*,BindingList*>::DelIterator dIt(_skolemsByFreeVars);
  while (dIt.hasNext()) {
    VarSet* vars;
    BindingList* bindings;
    dIt.next(vars,bindings);
    bindings->destroy();
    dIt.del();
  }
}

void NewCNF::process(TermList ts, Occurrences &occurrences)
{
  CALL("NewCNF::process(TermList)");

  if (ts.isVar()) {
    processBoolVar(ts.var(), occurrences);
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
    introduceGenClause(GenLit(name, OPPOSITE(sign)), GenLit(g, sign));
  }

  occurrences.replaceBy(name);

  return name;
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

    default:
      ASSERTION_VIOLATION_REP(g->toString());
  }
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

  unsigned len = gc->size();
  for (unsigned i = 0; i < len; i++) {
    Formula* g = formula(gc->literals[i]);

    ASS_REP(g->connective() == LITERAL, g->toString());
    ASS_REP(g->literal()->shared(), g->toString());

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
