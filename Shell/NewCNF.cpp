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
#include "Lib/Metaiterators.hpp"
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

  ASS(_queue.isEmpty());
  _queue.push_back(f);

  SPGenClause topLevelSingleton = SPGenClause(new GenClause(f));

  ASS(_genClauses.empty());
  _genClauses.push_front(topLevelSingleton); //push_front, so that a followup begin() "points" here
  SPGenClauseLookup topLevelSingletonLookup(topLevelSingleton,_genClauses.begin(),0);

  Occurrences occurrences;
  SPGenClauseLookupList::push(topLevelSingletonLookup,occurrences.positiveOccurrences);
  occurrences.positiveCount++;

  ASS(_occurrences.isEmpty());
  ALWAYS(_occurrences.insert(f,occurrences));

  processAll();

  createClauses(output);

  _varSorts.reset();
  _freeVars.reset();
}

void NewCNF::processLiteral(Formula* g, Occurrences &occurrences)
{
  CALL("NewCNF::processLiteral");

  LOG2("processLiteral ",g->toString());

  ASS(g->connective() == LITERAL);

  // just delete occurrences to release the SPGenClauses

  for (SIGN sign : { NEGATIVE, POSITIVE }) {
    SPGenClauseLookupList* signOccurrences = occurrences.of(sign);
    signOccurrences->destroy();

    // TODO: could check in debug mode that the occurrences are valid
  }
}

void NewCNF::processAndOr(Formula* g, Occurrences &occurrences)
{
  CALL("NewCNF::processAndOr");

  LOG2("processAndOr ",g->toString());

  LOG2("occurrences.positiveCount ",occurrences.positiveCount);
  LOG2("occurrences.negativeCount ",occurrences.negativeCount);

  ASS(g->connective() == OR || g->connective() == AND);

  FormulaList* args = g->args();
  unsigned argLen = args->length();

  // update the queue and create Occurrences for sub-formulas here
  {
    FormulaList::Iterator it(args);
    while (it.hasNext()) {
      Formula* arg = it.next();
      _queue.push_back(arg);
      ALWAYS(_occurrences.insert(arg, Occurrences()));
    }
  }

  // start expanding for g

  SPGenClauseLookupList* toLinearize;   // the positive OR and negative AND
  SPGenClauseLookupList* toDistribute; // the negative AND and positive OR

  SIGN linearizationSign = g->connective() == OR ? POSITIVE : NEGATIVE; // == !distributeNegatively
  toLinearize  = occurrences.of(linearizationSign);
  toDistribute = occurrences.of(OPPOSITE(linearizationSign));

  // process toLinarize

  while (SPGenClauseLookupList::isNonEmpty(toLinearize)) {
    SPGenClauseLookup gcl = SPGenClauseLookupList::pop(toLinearize);

    SPGenClause gcOrig = gcl.gc;
    if (!gcOrig->valid) {
      continue;
    }

    gcOrig->valid = false;
    GenClauses::iterator gci = gcl.gci;
    _genClauses.erase(gci);

    DArray<GenLit>& litsOrig = gcOrig->lits;
    unsigned lenOrig = litsOrig.size();

    SPGenClause gcNew = SPGenClause(new GenClause(lenOrig+argLen-1,gcOrig->bindings));
    _genClauses.push_front(gcNew);

    DArray<GenLit>& litsNew = gcNew->lits;
    unsigned idx = 0;

    for (unsigned i = 0; i < lenOrig; i++) {
      GenLit gl = litsOrig[i];

      if (gl.first == g) {
        ASS_EQ(i,gcl.idx);
        ASS_EQ(gl.second, linearizationSign);

        // insert arguments instead of g here (and update occurrences)
        FormulaList::Iterator it(args);
        while (it.hasNext()) {
          Formula* arg = it.next();

          litsNew[idx] = make_pair(arg,linearizationSign);

          Occurrences &occurrences = _occurrences.get(arg);

          SPGenClauseLookupList::push(SPGenClauseLookup(gcNew,_genClauses.begin(),idx),
                                      occurrences.of(linearizationSign));
          occurrences.count(linearizationSign) += 1;

          idx++;
        }

      } else {
        litsNew[idx] = gl;

        Occurrences * litsInfo = _occurrences.findPtr(gl.first);
        if (litsInfo) {
          SPGenClauseLookupList::push(SPGenClauseLookup(gcNew,_genClauses.begin(),idx), litsInfo->of(gl.second));

          // the number of occurrences stays intact
        }

        idx++;
      }
    }
  }

  // process toDistribute

  while (SPGenClauseLookupList::isNonEmpty(toDistribute)) {
    SPGenClauseLookup gcl = SPGenClauseLookupList::pop(toDistribute);

    SPGenClause gcOrig = gcl.gc;
    if (!gcOrig->valid) {
      continue;
    }

    gcOrig->valid = false;
    GenClauses::iterator gci = gcl.gci;
    _genClauses.erase(gci);

    DArray<GenLit>& litsOrig = gcOrig->lits;
    unsigned lenOrig = litsOrig.size();

    // decrease number of occurrences by one for all literals in gcOrig
    for (unsigned i = 0; i < lenOrig; i++) {
      GenLit gl = litsOrig[i];

      Occurrences * litsInfo;
      if (gl.first != g && (litsInfo = _occurrences.findPtr(gl.first))) {
        litsInfo->count(gl.second) -= 1;
      }
    }

    FormulaList::Iterator it(args);
    while (it.hasNext()) {
      Formula* arg = it.next();

      SPGenClause gcNew = SPGenClause(new GenClause(lenOrig,gcOrig->bindings));
      _genClauses.push_front(gcNew);

      DArray<GenLit>& litsNew = gcNew->lits;
      for (unsigned i = 0; i < lenOrig; i++) {
        GenLit gl = litsOrig[i];

        if (gl.first == g) {
          ASS_EQ(i,gcl.idx);
          ASS_EQ(gl.second, OPPOSITE(linearizationSign));

          litsNew[i] = make_pair(arg,OPPOSITE(linearizationSign));

          Occurrences &occurrences = _occurrences.get(arg);
          SPGenClauseLookupList::push(SPGenClauseLookup(gcNew,_genClauses.begin(),i),
                                      occurrences.of(OPPOSITE(linearizationSign)));
          occurrences.count(OPPOSITE(linearizationSign)) += 1;
        } else {
          litsNew[i] = gl;

          Occurrences * litsInfo = _occurrences.findPtr(gl.first);
          if (litsInfo) {
            SPGenClauseLookupList::push(SPGenClauseLookup(gcNew,_genClauses.begin(),i), litsInfo->of(gl.second));
            litsInfo->count(gl.second) += 1;
          }
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

  Formula* left = g->left();
  _queue.push_back(left);
  ALWAYS(_occurrences.insert(left, Occurrences()));

  Formula* right = g->right();
  _queue.push_back(right);
  ALWAYS(_occurrences.insert(right, Occurrences()));

  // WARNING: what we do here is a bit fragile
  // the two calls to get need to be after the two calls to insert
  // as insert invalidates the references in general!
  Occurrences & leftOccInfo = _occurrences.get(left);
  Occurrences & rightOccInfo = _occurrences.get(right);

  // start expanding for g

  SPGenClauseLookupList* toProcess[2];  // the first is the IFF-like, the second the XOR-like

  SIGN sign = g->connective() == IFF ? POSITIVE : NEGATIVE;
  toProcess[0] = occurrences.of(sign);
  toProcess[1] = occurrences.of(OPPOSITE(sign));

  for (unsigned flip = 0; flip < 2; flip++) {
    SPGenClauseLookupList* current = toProcess[flip];

    while (SPGenClauseLookupList::isNonEmpty(current)) {
      SPGenClauseLookup gcl = SPGenClauseLookupList::pop(current);

      SPGenClause gcOrig = gcl.gc;
      if (!gcOrig->valid) {
        continue;
      }

      gcOrig->valid = false;
      GenClauses::iterator gci = gcl.gci;
      _genClauses.erase(gci);

      DArray<GenLit>& litsOrig = gcOrig->lits;
      unsigned lenOrig = litsOrig.size();

      SPGenClause gcNew1 = SPGenClause(new GenClause(lenOrig+1,gcOrig->bindings));
      _genClauses.push_front(gcNew1);
      GenClauses::iterator gciNew1 = _genClauses.begin();

      SPGenClause gcNew2 = SPGenClause(new GenClause(lenOrig+1,gcOrig->bindings));
      _genClauses.push_front(gcNew2);
      GenClauses::iterator gciNew2 = _genClauses.begin();

      DArray<GenLit>& litsNew1 = gcNew1->lits;
      DArray<GenLit>& litsNew2 = gcNew2->lits;
      unsigned idx = 0;

      for (unsigned i = 0; i < lenOrig; i++) {
        GenLit gl = litsOrig[i];

        if (gl.first == g) {
          ASS_EQ(i,gcl.idx);
          ASS_EQ(gl.second, (g->connective() == IFF) ^ (flip)); // positive occurrences in the first pass for IFF and the second pass for XOR

          litsNew1[idx] = make_pair(left,NEGATIVE);
          SPGenClauseLookupList::push(SPGenClauseLookup(gcNew1,gciNew1,idx),leftOccInfo.of(NEGATIVE));
          leftOccInfo.count(NEGATIVE) += 1;

          litsNew2[idx] = make_pair(left,POSITIVE);
          SPGenClauseLookupList::push(SPGenClauseLookup(gcNew2,gciNew2,idx),leftOccInfo.of(POSITIVE));
          leftOccInfo.count(POSITIVE) += 1;

          idx++;

          bool secondIn1st = !flip;
          litsNew1[idx] = make_pair(right,secondIn1st);
          SPGenClauseLookupList::push(SPGenClauseLookup(gcNew1,gciNew1,idx), rightOccInfo.of(secondIn1st));
          rightOccInfo.count(secondIn1st) += 1;

          bool secondIn2nd = flip;
          litsNew2[idx] = make_pair(right,secondIn2nd);
          SPGenClauseLookupList::push(SPGenClauseLookup(gcNew2,gciNew2,idx), rightOccInfo.of(secondIn2nd));
          rightOccInfo.count(secondIn2nd) += 1;

          idx++;
        } else {
          litsNew1[idx] = gl;
          litsNew2[idx] = gl;

          Occurrences * litsInfo = _occurrences.findPtr(gl.first);
          if (litsInfo) {
            SPGenClauseLookupList::push(SPGenClauseLookup(gcNew1,gciNew1,idx), litsInfo->of(gl.second));
            SPGenClauseLookupList::push(SPGenClauseLookup(gcNew2,gciNew2,idx), litsInfo->of(gl.second));

            litsInfo->count(gl.first) += 1; // just +1, for it was there already once
          }

          idx++;
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
    Formula* f = _beingClausified->formula();
    SortHelper::collectVariableSorts(f, _varSorts);
  }
}

Kernel::Term* NewCNF::createSkolemTerm(unsigned var, VarSet* free)
{
  CALL("NewCNF::createSkolemTerm");

  int arity = free->size();

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
        unsigned var = vs.next();
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

void NewCNF::processForallExists(Formula* g, Occurrences &occurrences)
{
  CALL("NewCNF::processForallExists");

  LOG2("processForallExists ",g->toString());

  ASS(g->connective() == FORALL || g->connective() == EXISTS);

  // update the queue and reuse (!) Occurrences for sub-formula

  Formula* qarg = g->qarg();
  _queue.push_back(qarg);

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

        DArray<GenLit>& litsOrig = gcOrig->lits;
        GenLit& gl = litsOrig[gcl.idx];
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

  ALWAYS(_occurrences.insert(qarg,occurrences)); // qarg is reusing g's occurrences (!)

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

  int length = free->size();
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

      SPGenClause gcOrig = gcl.gc;
      if (!gcOrig->valid) {
        // occsOld progresses and deletes its top
        SPGenClauseLookupList::pop(occsOld);
      } else {
        SPGenClauseLookupList* redirectTo = occsNew;
        occsNew = occsOld;
        // occsOld's tail goes to old occsNew and occsOld progresses
        occsOld = occsOld->setTail(redirectTo);

        DArray<GenLit>& litsOrig = gcOrig->lits;
        GenLit& gl = litsOrig[gcl.idx];
        ASS_EQ(gl.first,g);
        ASS_EQ(gl.second, sign);
        gl.first = name;
      }
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
    Formula* g = _queue.pop_front();
    Occurrences occurrences;
    ALWAYS(_occurrences.pop(g,occurrences));

    LOG1("processAll iteration; _genClauses:");
    for (SPGenClause gc : _genClauses ) {
      LOG1(gc->toString());
    }

    // the case of naming
    if ((_namingThreshold > 1) && g->connective() != LITERAL && occurrences.positiveCount + occurrences.negativeCount > _namingThreshold) {
      Formula* name = performNaming(g,occurrences);

      for (SIGN sign : { NEGATIVE, POSITIVE }) {
        if (occurrences.count(sign)) {
          // One could also consider the case where (part of) the bindings goes to the definition
          // which perhaps allows us to the have a skolem predicate with fewer arguments
          SPGenClause gcNew = SPGenClause(new GenClause(2,BindingList::empty()));

          _genClauses.push_front(gcNew);
          gcNew->lits[0] = make_pair(name, OPPOSITE(sign));
          gcNew->lits[1] = make_pair(g, sign);

          occurrences.count(sign) = 1;
          occurrences.of(sign) = new SPGenClauseLookupList(SPGenClauseLookup(gcNew, _genClauses.begin(), 1), 0);
        } else {
          occurrences.of(sign) = SPGenClauseLookupList::empty();
        }
      }

      LOG2("performedNaming for ",g->toString());
      for (SPGenClause gc : _genClauses ) {
        LOG1(gc->toString());
      }

      // keep on processing g, just in the definition, why not?

      // (name is just a literal an need not be touched)
      ASS_EQ(name->connective(),LITERAL);
    }

    // TODO: currently we don't check for tautologies, as there should be none appearing (we use polarity based expansion of IFF and XOR)

    switch (g->connective()) {
      case LITERAL:
        processLiteral(g,occurrences);
        break;

      case AND:
      case OR:
        processAndOr(g,occurrences);
        break;

      case IFF:
      case XOR:
        processIffXor(g,occurrences);
        break;

      case FORALL:
      case EXISTS:
        processForallExists(g,occurrences);
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
  for (SPGenClause gc : _genClauses ) {
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

    DArray<GenLit>& lits = gc->lits;
    unsigned len = lits.size();
    for (unsigned i = 0; i < len; i++) {
      GenLit gl = lits[i];

      Formula* g = gl.first;
      ASS_EQ(g->connective(), LITERAL);

      Literal* l = g->literal();
      l = l->apply(subst);
      if (!gl.second) { // negative occurrence
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



