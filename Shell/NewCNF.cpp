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

    ASS_REP(g->connective() != LITERAL, g->toString());

    LOG1("process() iteration; _genClauses:");
    for (SPGenClause gc : _genClauses) {
      LOG1(gc->toString());
    }

    if ((_namingThreshold > 1) && occurrences.size() > _namingThreshold) {
      nameSubformula(g, occurrences);
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

      default:
        ASSERTION_VIOLATION;
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
