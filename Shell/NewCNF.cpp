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

  SPGenClause gc = introduceGenClause(1, BindingList::empty());
  setLiteral(gc, 0, makeGenLit(f, POSITIVE));

  processAll();

  createClauses(output);

  _varSorts.reset();
  _freeVars.reset();
}

void NewCNF::processAndOr(JunctionFormula* g, Occurrences &occurrences)
{
  CALL("NewCNF::processAndOr");

  LOG2("processAndOr ",g->toString());

  LOG2("occurrences.positiveCount ",occurrences.positiveCount);
  LOG2("occurrences.negativeCount ",occurrences.negativeCount);

  // update the queue and create Occurrences for sub-formulas here
  {
    FormulaList::Iterator it(g->args());
    while (it.hasNext()) {
      enqueue(it.next());
    }
  }

  // start expanding for g
  SIGN flatteningSign = g->connective() == OR ? POSITIVE : NEGATIVE; // == !distributeNegatively

  // process toLinarize
  // the positive OR and negative AND
  OccurrenceList* flattenOccurrences = occurrences.of(flatteningSign);

  while (OccurrenceList::isNonEmpty(flattenOccurrences)) {
    Occurrence occ = OccurrenceList::pop(flattenOccurrences);

    if (!occ.valid()) {
      continue;
    }

    invalidate(occ);

    unsigned processedGcSize = (unsigned) occ.gc->literals.size() + g->args()->length() - 1;
    SPGenClause processedGc = introduceGenClause(processedGcSize, occ.gc->bindings);

    unsigned position = 0;
    for (unsigned i = 0; i < occ.gc->literals.size(); i++) {
      Formula* f = occ.gc->literals[i].first;
      SIGN sign  = occ.gc->literals[i].second;

      if (f == g) {
        ASS_EQ(i, occ.position);
        ASS_EQ(sign, flatteningSign);

        // insert arguments instead of g here (and update occurrences)
        FormulaList::Iterator it(g->args());
        while (it.hasNext()) {
          setLiteral(processedGc, position++, makeGenLit(it.next(), flatteningSign));
        }
      } else {
        setLiteral(processedGc, position++, occ.gc->literals[i], false);
      }
    }
  }

  // process distributeOccurrences
  // the negative AND and positive OR
  OccurrenceList* distributeOccurrences = occurrences.of(OPPOSITE(flatteningSign));

  while (OccurrenceList::isNonEmpty(distributeOccurrences)) {
    Occurrence occ = OccurrenceList::pop(distributeOccurrences);

    if (!occ.valid()) {
      continue;
    }

    invalidate(occ);

    unsigned nrLiterals = (unsigned) occ.gc->literals.size();

    // decrease number of occurrences by one for all literals in gc
    for (unsigned i = 0; i < nrLiterals; i++) {
      Formula* f = occ.gc->literals[i].first;
      SIGN sign  = occ.gc->literals[i].second;

      if (f != g) {
        Occurrences* gcOccurrences = _occurrences.findPtr(f);
        if (gcOccurrences) {
          gcOccurrences->decrement(sign);
        }
      }
    }

    FormulaList::Iterator it(g->args());
    while (it.hasNext()) {
      Formula* arg = it.next();

      SPGenClause processedGc = introduceGenClause(nrLiterals, occ.gc->bindings);

      for (unsigned i = 0; i < nrLiterals; i++) {
        Formula* f = occ.gc->literals[i].first;
        SIGN sign  = occ.gc->literals[i].second;

        if (f == g) {
          ASS_EQ(i, occ.position);
          ASS_EQ(sign, OPPOSITE(flatteningSign));
          setLiteral(processedGc, i, makeGenLit(arg, OPPOSITE(flatteningSign)));
        } else {
          setLiteral(processedGc, i, occ.gc->literals[i]);
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

  enqueue(g->left());
  enqueue(g->right());

  // start expanding for g

  SIGN formulaSign = g->connective() == IFF ? POSITIVE : NEGATIVE;

  for (SIGN occurrenceSign : { POSITIVE, NEGATIVE }) {
    OccurrenceList* signOccurrences = occurrences.of(occurrenceSign);

    while (OccurrenceList::isNonEmpty(signOccurrences)) {
      Occurrence occ = OccurrenceList::pop(signOccurrences);

      if (!occ.valid()) {
        continue;
      }

      invalidate(occ);

      for (SIDE side : { LEFT, RIGHT }) {
        SPGenClause processedGc = introduceGenClause((unsigned) occ.gc->literals.size() + 1, occ.gc->bindings);
        for (unsigned i = 0, position = 0; i < occ.gc->literals.size(); i++, position++) {
          Formula* f = occ.gc->literals[i].first;
          SIGN sign  = occ.gc->literals[i].second;

          if (f == g) {
            ASS_EQ(i, occ.position);
            ASS_EQ(sign, formulaSign != occurrenceSign ? POSITIVE : NEGATIVE);

            SIGN lhsSign = side == LEFT ? NEGATIVE : POSITIVE;
            setLiteral(processedGc, position++, makeGenLit(g->left(), lhsSign));

            SIGN rhsSign = side == LEFT ? OPPOSITE(occurrenceSign) : occurrenceSign;
            setLiteral(processedGc, position, makeGenLit(g->right(), rhsSign));
          } else {
            setLiteral(processedGc, position, occ.gc->literals[i], side == LEFT);
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

  BindingList* newBindings;

  if (!_skolemsByBindings.find(bindings,newBindings)) {
    // first level cache miss, construct free variable set

    VarSet* gVars = freeVars(g);

    BindingList::Iterator bIt(bindings);
    VarSet* bVars = (VarSet*) VarSet::getFromIterator(getMappingIterator(bIt, BindingGetFirstFunctor()));

    VarSet* actualFreeVars = (VarSet*) gVars->subtract(bVars);

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
    OccurrenceList* signOccurrences = occurrences.of(sign);
    OccurrenceList* processedOccurrences = nullptr;

    while (OccurrenceList::isNonEmpty(signOccurrences)) {
      Occurrence occ = signOccurrences->head();

      if (!occ.valid()) {
        // signOccurrences progresses and deletes its top
        OccurrenceList::pop(signOccurrences);
        continue;
      }

      OccurrenceList * redirectTo = processedOccurrences;
      processedOccurrences = signOccurrences;
      // signOccurrences's tail goes to old processedOccurrences and signOccurrences progresses
      signOccurrences = signOccurrences->setTail(redirectTo);

      GenLit& gl = occ.gc->literals[occ.position];
      ASS_EQ(gl.first,g);
      ASS_EQ(gl.second, sign);
      gl.first = qarg;

      if ((sign == POSITIVE) == (g->connective() == EXISTS)) {
        skolemise(g, occ.gc->bindings);
      }
    }

    occurrences.of(sign) = processedOccurrences;

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
    OccurrenceList* signOccurrences = occurrences.of(sign);
    OccurrenceList* processedOccurrences = nullptr;

    while (OccurrenceList::isNonEmpty(signOccurrences)) {
      Occurrence occ = signOccurrences->head();

      if (!occ.valid()) {
        // signOccurrences progresses and deletes its top
        OccurrenceList::pop(signOccurrences);
        continue;
      }

      OccurrenceList* redirectTo = processedOccurrences;
      processedOccurrences = signOccurrences;
      // signOccurrences's tail goes to old processedOccurrences and signOccurrences progresses
      signOccurrences = signOccurrences->setTail(redirectTo);

      GenLit& gl = occ.gc->literals[occ.position];
      ASS_EQ(gl.first,g);
      ASS_EQ(gl.second, sign);
      gl.first = name;
    }
    occurrences.of(sign) = processedOccurrences;
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

    ASS_REP(g->connective() != LITERAL, g->toString());

    LOG1("processAll iteration; _genClauses:");
    for (SPGenClause gc : _genClauses) {
      LOG1(gc->toString());
    }

    // the case of naming
    if ((_namingThreshold > 1) && occurrences.count() > _namingThreshold) {
      Formula* name = performNaming(g,occurrences);
      ASS_EQ(name->connective(),LITERAL);

      for (SIGN sign : { NEGATIVE, POSITIVE }) {
        if (!occurrences.anyOf(sign)) {
          occurrences.of(sign) = OccurrenceList::empty();
          continue;
        }

        // One could also consider the case where (part of) the bindings goes to the definition
        // which perhaps allows us to the have a skolem predicate with fewer arguments
        SPGenClause gc = introduceGenClause(2, BindingList::empty());
        setLiteral(gc, 0, makeGenLit(name, OPPOSITE(sign)));
        setLiteral(gc, 1, makeGenLit(g, sign));
      }

      LOG2("performedNaming for ",g->toString());
      for (SPGenClause gc : _genClauses) {
        LOG1(gc->toString());
      }

      // keep on processing g, just in the definition, why not?
    }

    // TODO: currently we don't check for tautologies, as there should be none appearing (we use polarity based expansion of IFF and XOR)

    switch (g->connective()) {
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
