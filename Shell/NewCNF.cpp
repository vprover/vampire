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
      Clause* clause = new(0) Clause(0,
             unit->inputType(),
             new Inference1(Inference::CLAUSIFY,unit));
      output.push(clause);
    }
    return;
  default:
    break;
  }

  SPGenClause topLevelSingleton = SPGenClause(new GenClause(f));

  ASS(_genClauses.empty());
  _genClauses.push_front(topLevelSingleton); //push_front, so that a followup begin() "points" here
  SPGenClauseLookup topLevelSingletonLookup(topLevelSingleton,_genClauses.begin(),0);

  Occurrences occurrences;
  occurrences.add(POSITIVE, topLevelSingletonLookup);

  ASS(_queue.isEmpty());
  ASS(_occurrences.isEmpty());
  enqueue(f, occurrences);

  processAll();

  createClauses(output);

  _varSorts.reset();
  _freeVars.reset();
}

void NewCNF::processLiteral(Literal* l, Occurrences &occurrences)
{
  CALL("NewCNF::processLiteral");

  LOG2("processLiteral ",l->toString());

  // just delete occurrences to release the SPGenClauses

  for (SIGN sign : { NEGATIVE, POSITIVE }) {
    occurrences.of(sign)->destroy();
    // TODO: could check in debug mode that the occurrences are valid
  }
}

void NewCNF::processAndOr(JunctionFormula* g, Occurrences &occurrences)
{
  CALL("NewCNF::processAndOr");

  LOG2("processAndOr ",g->toString());

  LOG2("occurrences.positiveCount ",occurrences.positiveCount);
  LOG2("occurrences.negativeCount ",occurrences.negativeCount);

  FormulaList* args = g->args();

  // update the queue and create Occurrences for sub-formulas here
  {
    FormulaList::Iterator it(args);
    while (it.hasNext()) {
      enqueue(it.next());
    }
  }

  // start expanding for g
  SIGN linearizationSign = g->connective() == OR ? POSITIVE : NEGATIVE; // == !distributeNegatively

  // process toLinarize
  // the positive OR and negative AND
  SPGenClauseLookupList* toLinearize = occurrences.of(linearizationSign);

  while (SPGenClauseLookupList::isNonEmpty(toLinearize)) {
    SPGenClauseLookup gcl = SPGenClauseLookupList::pop(toLinearize);

    if (!gcl.valid()) {
      continue;
    }

    invalidate(gcl);

    unsigned processedGcSize = (unsigned)gcl.gc->literals.size() + args->length() - 1;
    SPGenClause processedGc = SPGenClause(new GenClause(processedGcSize, gcl.gc->bindings));
    _genClauses.push_front(processedGc);

    unsigned position = 0;
    for (unsigned i = 0; i < gcl.gc->literals.size(); i++) {
      Formula* f = gcl.gc->literals[i].first;
      SIGN sign  = gcl.gc->literals[i].second;

      if (f == g) {
        ASS_EQ(i,gcl.idx);
        ASS_EQ(sign, linearizationSign);

        // insert arguments instead of g here (and update occurrences)
        FormulaList::Iterator it(args);
        while (it.hasNext()) {
          setLiteral(processedGc, position++, it.next(), linearizationSign);
        }
      } else {
        processedGc->literals[position] = gcl.gc->literals[i];

        Occurrences* gcOccurrences = _occurrences.findPtr(f);
        if (gcOccurrences) {
          gcOccurrences->add(sign, SPGenClauseLookup(processedGc, _genClauses.begin(), position), false);
        }

        position++;
      }
    }
  }

  // process toDistribute
  // the negative AND and positive OR
  SPGenClauseLookupList* toDistribute = occurrences.of(OPPOSITE(linearizationSign));

  while (SPGenClauseLookupList::isNonEmpty(toDistribute)) {
    SPGenClauseLookup gcl = SPGenClauseLookupList::pop(toDistribute);

    if (!gcl.valid()) {
      continue;
    }

    invalidate(gcl);

    unsigned nrLiterals = (unsigned) gcl.gc->literals.size();

    // decrease number of occurrences by one for all literals in gc
    for (unsigned i = 0; i < nrLiterals; i++) {
      Formula* f = gcl.gc->literals[i].first;
      SIGN sign  = gcl.gc->literals[i].second;

      if (f != g) {
        Occurrences* gcOccurrences = _occurrences.findPtr(f);
        if (gcOccurrences) {
          gcOccurrences->decrement(sign);
        }
      }
    }

    FormulaList::Iterator it(args);
    while (it.hasNext()) {
      Formula* arg = it.next();

      SPGenClause processedGc = SPGenClause(new GenClause(nrLiterals, gcl.gc->bindings));
      _genClauses.push_front(processedGc);

      for (unsigned i = 0; i < nrLiterals; i++) {
        Formula* f = gcl.gc->literals[i].first;
        SIGN sign  = gcl.gc->literals[i].second;

        if (f == g) {
          ASS_EQ(i,gcl.idx);
          ASS_EQ(sign, OPPOSITE(linearizationSign));
          setLiteral(processedGc, i, arg, OPPOSITE(linearizationSign));
        } else {
          setLiteral(processedGc, i, f, sign);
        }
      }
    }
  }
}

void NewCNF::processIffXor(Formula* g, Occurrences &occurrences)
{
  CALL("NewCNF::processIffXor");

  LOG2("processIffXor ",g->toString());

  ASS(g->connective() == IFF || g->connective() == XOR);

  // update the queue and create Occurrences for sub-formulas here

  Formula* lhs = g->left();
  enqueue(lhs);

  Formula* rhs = g->right();
  enqueue(rhs);

  // start expanding for g

  SIGN formulaSign = g->connective() == IFF ? POSITIVE : NEGATIVE;

  for (SIGN occurrenceSign : { POSITIVE, NEGATIVE }) {
    SPGenClauseLookupList* gcls = occurrences.of(occurrenceSign);

    while (SPGenClauseLookupList::isNonEmpty(gcls)) {
      SPGenClauseLookup gcl = SPGenClauseLookupList::pop(gcls);

      if (!gcl.valid()) {
        continue;
      }

      invalidate(gcl);

      SPGenClause processedGc[2];
      for (SIDE side : { LEFT, RIGHT }) {
        processedGc[side] = SPGenClause(new GenClause((unsigned) gcl.gc->literals.size() + 1, gcl.gc->bindings));
        _genClauses.push_front(processedGc[side]);
      }

      for (SIDE side : { LEFT, RIGHT }) {
        for (unsigned i = 0, position = 0; i < gcl.gc->literals.size(); i++, position++) {
          Formula* f = gcl.gc->literals[i].first;
          SIGN sign  = gcl.gc->literals[i].second;

          if (f == g) {
            ASS_EQ(i, gcl.idx);
            ASS_EQ(sign, formulaSign != occurrenceSign ? POSITIVE : NEGATIVE);

            SIGN lhsSign = side == LEFT ? NEGATIVE : POSITIVE;
            SIGN rhsSign = side == LEFT ? OPPOSITE(occurrenceSign) : occurrenceSign;

            setLiteral(processedGc[side], position++, lhs, lhsSign);
            setLiteral(processedGc[side], position,   rhs, rhsSign);
          } else {
            processedGc[side]->literals[position] = gcl.gc->literals[i];
            Occurrences* gcOccurrences = _occurrences.findPtr(f);
            if (gcOccurrences) {
              // do not increment the counter, for it was there already once
              gcOccurrences->add(sign, SPGenClauseLookup(processedGc[side], _genClauses.begin(), position), side == LEFT);
            }
          }
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
        Literal* l = g->literal();
        VariableIterator vit(l);
        static Stack<unsigned> is;
        is.reset();
        while (vit.hasNext()) {
          is.push(vit.next().var());
        }
        res = VarSet::getFromArray(is.begin(),is.size());
        break;
      }
      case AND:
      case OR: {
        FormulaList::Iterator aIt(g->args());
        ASS(aIt.hasNext());
        res = freeVars(aIt.next());
        while (aIt.hasNext()) {
          res = res->getUnion(freeVars(aIt.next()));
        }
        break;
      }
      case IFF:
      case XOR: {
        res = freeVars(g->left());
        res = res->getUnion(freeVars(g->right()));
        break;
      }
      case FORALL:
      case EXISTS: {
        res = freeVars(g->qarg());
        Formula::VarList::Iterator vit(g->vars());
        res = res->subtract(VarSet::getFromIterator(vit));
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
void NewCNF::skolemise(Formula* g, BindingList*& bindings)
{
  CALL("NewCNF::skolemise");

  ASS(g->connective() == FORALL || g->connective() == EXISTS);

  BindingList* newBindings;

  if (!_skolemsByBindings.find(bindings,newBindings)) {
    // first level cache miss, construct free variable set

    VarSet* gVars = freeVars(g);

    BindingList::Iterator bIt(bindings);
    VarSet* bVars = VarSet::getFromIterator(getMappingIterator(bIt,BindingGetFirstFunctor()));

    VarSet* actualFreeVars = gVars->subtract(bVars);

    if (!_skolemsByFreeVars.find(actualFreeVars,newBindings)) {
      // second level cache miss, let's do the actual skolemisation

      newBindings = nullptr;

      Formula::VarList::Iterator vs(g->vars());
      while (vs.hasNext()) {
        unsigned var = (unsigned)vs.next();
        Term* skolemTerm = createSkolemTerm(var,actualFreeVars);
        BindingList::push(make_pair(var,skolemTerm),newBindings);
      }

      // store the results in the caches
      _skolemsByFreeVars.insert(actualFreeVars,newBindings);
    }

    _skolemsByBindings.insert(bindings,newBindings);
  }

  // extend the given binding
  BindingList::Iterator it(newBindings);
  while (it.hasNext()) {
    BindingList::push(it.next(),bindings);
  }
}

void NewCNF::processForallExists(QuantifiedFormula* g, Occurrences &occurrences)
{
  CALL("NewCNF::processForallExists");

  LOG2("processForallExists ",g->toString());

  // update the queue and reuse (!) Occurrences for sub-formula

  Formula* qarg = g->qarg();
  enqueue(qarg, occurrences); // qarg is reusing g's occurrences (!)

  // the skolem caches are empty
  ASS(_skolemsByBindings.isEmpty());
  ASS(_skolemsByFreeVars.isEmpty());

  // Correct all the GenClauses to mention qarg instead of g
  // (drop references to invalid ones)
  //
  // In the skolemising polarity introduce new skolems as you go
  // each occurrence may need a new set depending on bindings,
  // but let's try to share as much as possible
  for (SIGN sign : { NEGATIVE, POSITIVE }) {
    SPGenClauseLookupList* occsOld = occurrences.of(sign);
    SPGenClauseLookupList* occsNew = nullptr;

    while (SPGenClauseLookupList::isNonEmpty(occsOld)) {
      SPGenClauseLookup gcl = occsOld->head();

      SPGenClause gcOrig = gcl.gc;
      if (!gcOrig->valid) {
        // occsOld progresses and deletes its top
        SPGenClauseLookupList::pop(occsOld);
      } else {
        SPGenClauseLookupList* redirectTo = occsNew;
        occsNew = occsOld;
        // occsOld's tail goes to old occsNew and occsOld progresses
        occsOld = occsOld->setTail(redirectTo);

        GenLit& gl = gcOrig->literals[gcl.idx];
        ASS_EQ(gl.first,g);
        ASS_EQ(gl.second, sign);
        gl.first = qarg;

        if (sign == (g->connective() == EXISTS)) { // skolemising
          skolemise(g,gcOrig->bindings);
        }
      }
    }
    occurrences.of(sign) = occsNew;

    // occCnts remain the same
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
Formula* NewCNF::performNaming(Kernel::Formula* g, Occurrences &occurrences)
{
  CALL("NewCNF::performNaming");

  ASS_NEQ(g->connective(), LITERAL);
  ASS_NEQ(g->connective(), NOT);

  VarSet* free = freeVars(g);
  Literal* atom = createNamingLiteral(g, free);
  Formula* name = new AtomicFormula(atom);

  // Correct all the GenClauses to mention name instead of g
  // (drop references to invalid ones)
  for (SIGN sign : { NEGATIVE, POSITIVE }) {
    SPGenClauseLookupList* occsOld = occurrences.of(sign);
    SPGenClauseLookupList* occsNew = nullptr;

    while (SPGenClauseLookupList::isNonEmpty(occsOld)) {
      SPGenClauseLookup gcl = occsOld->head();

      SPGenClause gc = gcl.gc;
      if (!gc->valid) {
        // occsOld progresses and deletes its top
        SPGenClauseLookupList::pop(occsOld);
        continue;
      }

      SPGenClauseLookupList* redirectTo = occsNew;
      occsNew = occsOld;
      // occsOld's tail goes to old occsNew and occsOld progresses
      occsOld = occsOld->setTail(redirectTo);

      GenLit& gl = gc->literals[gcl.idx];
      ASS_EQ(gl.first,g);
      ASS_EQ(gl.second, sign);
      gl.first = name;
    }
    occurrences.of(sign) = occsNew;

    // occCnts remain the same
  }

  return name;
}

void NewCNF::processAll()
{
  CALL("NewCNF::processAll");

  // process the generalized clauses until they contain only literals
  while(_queue.isNonEmpty()) {
    Formula* g;
    Occurrences occurrences;
    dequeue(g, occurrences);

    LOG1("processAll iteration; _genClauses:");
    for (SPGenClause gc : _genClauses) {
      LOG1(gc->toString());
    }

    // the case of naming
    if ((_namingThreshold > 1) && g->connective() != LITERAL && occurrences.count() > _namingThreshold) {
      Formula* name = performNaming(g,occurrences);

      for (SIGN sign : { NEGATIVE, POSITIVE }) {
        if (!occurrences.anyOf(sign)) {
          occurrences.of(sign) = SPGenClauseLookupList::empty();
          continue;
        }

        // One could also consider the case where (part of) the bindings goes to the definition
        // which perhaps allows us to the have a skolem predicate with fewer arguments
        SPGenClause gcNew = SPGenClause(new GenClause(2,BindingList::empty()));
        _genClauses.push_front(gcNew);

        gcNew->literals[0] = make_pair(name, OPPOSITE(sign));
        gcNew->literals[1] = make_pair(g, sign);

        occurrences.add(sign, SPGenClauseLookup(gcNew, _genClauses.begin(), 1));
      }

      LOG2("performedNaming for ",g->toString());
      for (SPGenClause gc : _genClauses) {
        LOG1(gc->toString());
      }

      // keep on processing g, just in the definition, why not?

      // (name is just a literal an need not be touched)
      ASS_EQ(name->connective(),LITERAL);
    }

    // TODO: currently we don't check for tautologies, as there should be none appearing (we use polarity based expansion of IFF and XOR)

    switch (g->connective()) {
      case LITERAL:
        processLiteral(g->literal(),occurrences);
        break;

      case AND:
      case OR:
        processAndOr(static_cast<JunctionFormula*>(g),occurrences);
        break;

      case IFF:
      case XOR:
        processIffXor(g,occurrences);
        break;

      case FORALL:
      case EXISTS:
        processForallExists(static_cast<QuantifiedFormula*>(g),occurrences);
        break;

      default:
        ASSERTION_VIOLATION;
    }
  }
}

void NewCNF::createClauses(Stack<Clause*>& output)
{
  CALL("NewCNF::createClauses");

  static Substitution subst;
  ASS(subst.isEmpty());
  for (SPGenClause gc : _genClauses) {
    LOG2("createClause for ",gc->toString());

    // prepare subst

    BindingList::Iterator bIt(gc->bindings);
    while (bIt.hasNext()) {
      Binding b = bIt.next();
      subst.bind(b.first,b.second);
    }

    // TODO: since the bindings are share, there is no easy way to delete them

    // transform to actual clause

    static Stack<Literal*> literals;
    ASS(literals.isEmpty());

    unsigned len = (unsigned) gc->literals.size();
    for (unsigned i = 0; i < len; i++) {
      Formula* g = gc->literals[i].first;
      SIGN  sign = gc->literals[i].second;

      ASS_EQ(g->connective(), LITERAL);

      Literal* l = g->literal();
      l = l->apply(subst);
      if (sign == NEGATIVE) {
        l = Literal::complementaryLiteral(l);
      }

      literals.push(l);
    }

    Clause* clause = new(len) Clause(len,_beingClausified->inputType(),
                                    new Inference1(Inference::CLAUSIFY,_beingClausified));
    for (int i = len-1;i >= 0;i--) {
      (*clause)[i] = literals[i];
    }

    output.push(clause);

    literals.reset();
    subst.reset();
  }
  _genClauses.clear();
}

}
