/**
 * @file NewCNF.cpp
 * Implements class NewCNF implementing the new CNF transformation.
 * @since 19/11/2015 Manchester
 */

#include "Debug/Tracer.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "NewCNF.hpp"

using namespace Lib;
using namespace Kernel;

namespace Shell {

void NewCNF::clausify(FormulaUnit* unit,Stack<Clause*>& output)
{
  CALL("NewCNF::clausify");

  Formula* f = unit->formula();

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

  OccInfo occInfo;
  SPGenClauseLookupList::push(topLevelSingletonLookup,occInfo.posOccs);
  occInfo.posCnt++;

  ASS(_occurences.isEmpty());
  ALWAYS(_occurences.insert(f,occInfo));

  processAll();

  createClauses(output);
}

void NewCNF::processLiteral(Formula* g, OccInfo& occInfo)
{
  CALL("NewCNF::processLiteral");

  ASS(g->connective() == LITERAL);

  // just delete occInfo to release the SPGenClauses

  for (bool positive : { false, true }) {
    SPGenClauseLookupList* occs = occInfo.occs(positive);
    occs->destroy();

    // TODO: could check in debug mode that the occurrences are valid
  }
}

void NewCNF::processAndOr(Formula* g, OccInfo& occInfo)
{
  CALL("NewCNF::processAndOr");

  ASS(g->connective() == OR || g->connective() == AND);

  FormulaList* args = g->args();
  unsigned argLen = args->length();

  // update the queue and create OccInfo for sub-formulas here
  {
    FormulaList::Iterator it(args);
    while (it.hasNext()) {
      Formula* arg = it.next();
      _queue.push_back(arg);
      ALWAYS(_occurences.insert(arg,OccInfo()));
    }
  }

  // start expanding for g

  SPGenClauseLookupList* toLinearize;   // the positive OR and negative AND
  SPGenClauseLookupList* toDistribute; // the negative AND and positive OR
  bool linearizePositively; // == !distributeNegatively

  if (g->connective() == OR) {
    toLinearize = occInfo.posOccs;
    toDistribute = occInfo.negOccs;
    linearizePositively = true;
  } else {
    toLinearize = occInfo.negOccs;
    toDistribute = occInfo.posOccs;
    linearizePositively = false;
  }

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

    SPGenClause gcNew = SPGenClause(new GenClause(lenOrig+argLen-1));
    _genClauses.push_front(gcNew);

    DArray<GenLit>& litsNew = gcNew->lits;
    unsigned idx = 0;

    for (unsigned i = 0; i < lenOrig; i++) {
      GenLit gl = litsOrig[i];

      if (gl.first == g) {
        ASS_EQ(i,gcl.idx);
        ASS_EQ(gl.second, linearizePositively);

        // insert arguments instead of g here (and update occurrences)
        FormulaList::Iterator it(args);
        while (it.hasNext()) {
          Formula* arg = it.next();

          litsNew[idx] = make_pair(arg,linearizePositively);

          OccInfo& occInfo = _occurences.get(arg);

          SPGenClauseLookupList::push(SPGenClauseLookup(gcNew,_genClauses.begin(),idx),occInfo.occs(linearizePositively));
          occInfo.cnt(linearizePositively) += 1;

          idx++;
        }

      } else {
        litsNew[idx] = gl;

        OccInfo& occInfo = _occurences.get(gl.first);

        SPGenClauseLookupList::push(SPGenClauseLookup(gcNew,_genClauses.begin(),idx),occInfo.occs(gl.second));

        // the number of occurrences stays intact

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
    // (this also touches the literal where g sits, but we don't care)
    for (unsigned i = 0; i < lenOrig; i++) {
      GenLit gl = litsOrig[i];
      OccInfo& occInfo = _occurences.get(gl.first);
      occInfo.cnt(gl.second) -= 1;
    }

    FormulaList::Iterator it(args);
    while (it.hasNext()) {
      Formula* arg = it.next();

      SPGenClause gcNew = SPGenClause(new GenClause(lenOrig));
      _genClauses.push_front(gcNew);

      DArray<GenLit>& litsNew = gcNew->lits;
      for (unsigned i = 0; i < lenOrig; i++) {
        GenLit gl = litsOrig[i];

        if (gl.first == g) {
          ASS_EQ(i,gcl.idx);
          ASS_EQ(gl.second, !linearizePositively);

          litsNew[i] = make_pair(arg,!linearizePositively);

          OccInfo& occInfo = _occurences.get(arg);
          SPGenClauseLookupList::push(SPGenClauseLookup(gcNew,_genClauses.begin(),i),occInfo.occs(!linearizePositively));
          occInfo.cnt(!linearizePositively) += 1;
        } else {
          litsNew[i] = gl;

          OccInfo& occInfo = _occurences.get(gl.first);
          SPGenClauseLookupList::push(SPGenClauseLookup(gcNew,_genClauses.begin(),i),occInfo.occs(gl.second));
          occInfo.cnt(gl.second) += 1;
        }
      }
    }
  }
}

void NewCNF::processIffXor(Formula* g, OccInfo& occInfo)
{
  CALL("NewCNF::processIffXor");

  ASS(g->connective() == IFF || g->connective() == XOR);

  // update the queue and create OccInfo for sub-formulas here

  Formula* left = g->left();
  _queue.push_back(left);
  ALWAYS(_occurences.insert(left,OccInfo()));
  OccInfo& leftOccInfo = _occurences.get(left);

  Formula* right = g->right();
  _queue.push_back(right);
  ALWAYS(_occurences.insert(right,OccInfo()));
  OccInfo& rightOccInfo = _occurences.get(right);

  // start expanding for g

  SPGenClauseLookupList* toProcess[2];  // the first is the IFF-like, the second the XOR-like

  if (g->connective() == IFF) {
    toProcess[0] = occInfo.posOccs;
    toProcess[1] = occInfo.negOccs;
  } else {
    toProcess[0] = occInfo.negOccs;
    toProcess[1] = occInfo.posOccs;
  }

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

      SPGenClause gcNew1 = SPGenClause(new GenClause(lenOrig+1));
      _genClauses.push_front(gcNew1);
      GenClauses::iterator gciNew1 = _genClauses.begin();

      SPGenClause gcNew2 = SPGenClause(new GenClause(lenOrig+1));
      _genClauses.push_front(gcNew2);
      GenClauses::iterator gciNew2 = _genClauses.begin();

      DArray<GenLit>& litsNew1 = gcNew1->lits;
      DArray<GenLit>& litsNew2 = gcNew2->lits;
      unsigned idx = 0;

      for (unsigned i = 0; i < lenOrig; i++) {
        GenLit gl = litsOrig[i];

        if (gl.first == g) {
          ASS_EQ(i,gcl.idx);
          ASS_EQ(gl.second, (g->connective() == IFF) ^ (!flip)); // positive occurrences in the first pass for IFF and the second pass for XOR

          litsNew1[idx] = make_pair(left,false);
          SPGenClauseLookupList::push(SPGenClauseLookup(gcNew1,gciNew1,idx),leftOccInfo.occs(false));
          leftOccInfo.cnt(false) += 1;

          litsNew2[idx] = make_pair(left,true);
          SPGenClauseLookupList::push(SPGenClauseLookup(gcNew2,gciNew2,idx),leftOccInfo.occs(true));
          leftOccInfo.cnt(true) += 1;

          idx++;

          bool secondIn1st = !flip;
          litsNew1[idx] = make_pair(right,secondIn1st);
          SPGenClauseLookupList::push(SPGenClauseLookup(gcNew1,gciNew1,idx),rightOccInfo.occs(secondIn1st));
          rightOccInfo.cnt(secondIn1st) += 1;

          bool secondIn2nd = flip;
          litsNew2[idx] = make_pair(right,secondIn2nd);
          SPGenClauseLookupList::push(SPGenClauseLookup(gcNew2,gciNew2,idx),rightOccInfo.occs(secondIn2nd));
          rightOccInfo.cnt(secondIn2nd) += 1;

          idx++;
        } else {
          litsNew1[idx] = gl;
          litsNew2[idx] = gl;

          OccInfo& occInfo = _occurences.get(gl.first);
          SPGenClauseLookupList::push(SPGenClauseLookup(gcNew1,gciNew1,idx),occInfo.occs(gl.second));
          SPGenClauseLookupList::push(SPGenClauseLookup(gcNew2,gciNew2,idx),occInfo.occs(gl.second));

          occInfo.cnt(gl.first) += 1; // just +1, for it was there already once

          idx++;
        }
      }
    }
  }
}

void NewCNF::processForallExists(Formula* g, OccInfo& occInfo)
{
  CALL("NewCNF::processForallExists");

  ASS(g->connective() == FORALL || g->connective() == EXISTS);

  // update the queue and reuse (!) OccInfo for sub-formula

  Formula* qarg = g->qarg();
  _queue.push_back(qarg);








  // TODO: will need to introduce the binding literals here

  // start by having a SPECIAL polarity for GenLits to mark binding literals for fast recognition








  // correct all the GenClauses to mention qarg instead of g
  // (drop references to invalid ones)
  for (bool positive : { false, true }) {
    SPGenClauseLookupList* occsOld = occInfo.occs(positive);
    SPGenClauseLookupList* occsNew = nullptr;

    while (SPGenClauseLookupList::isNonEmpty(occsOld)) {
      SPGenClauseLookup gcl = occsOld->head();

      SPGenClause gcOrig = gcl.gc;
      if (!gcOrig->valid) {
        // occsOld progresses and deletes its top
        SPGenClauseLookupList::pop(occsOld);
        continue;
      } else {
        // occsOld's top goes to occsNew and occsOld progresses
        occsOld = occsOld->setTail(occsNew);

        DArray<GenLit>& litsOrig = gcOrig->lits;
        GenLit& gl = litsOrig[gcl.idx];
        ASS_EQ(gl.first,g);
        ASS_EQ(gl.second,positive);
        gl.first = qarg;
      }
    }
    // occCnts remain the same
  }

  ALWAYS(_occurences.insert(qarg,occInfo)); // qarg is reusing g's occInfo (!)

  // start skolemising for g

  // FORALL and positive, EXISTS and negative
  // just drop the prefix

  // FORALL and negative, EXISTS and positive
  // Is there any occurrence at all?
  // If yes, introduce the skolem (Where do we get the variables from?)

}

void NewCNF::processAll()
{
  CALL("NewCNF::processAll");

  // process the generalized clauses until they contain only literals
  while(_queue.isNonEmpty()) {
    Formula* g = _queue.pop_front();
    OccInfo occInfo;
    ALWAYS(_occurences.pop(g,occInfo));

    // TODO: naming magic, based on occurrence counts
    // (Don't name literals. It is silly.)

    // TODO: currently we don't check for tautologies, as there should be none appearing (we use polarity based expansion of IFF and XOR)

    switch (g->connective()) {
      case LITERAL:
        processLiteral(g,occInfo);
        break;

      case AND:
      case OR:
        processAndOr(g,occInfo);
        break;

      case IFF:
      case XOR:
        processIffXor(g,occInfo);
        break;

      case FORALL:
      case EXISTS:
        processForallExists(g,occInfo);
        break;

      default:
        ASSERTION_VIOLATION;
    }
  }
}

void NewCNF::createClauses(Stack<Clause*>& output)
{
  CALL("NewCNF::createClauses");

  // produce clauses out of the generalized ones (while are now flat)

  // careful about double negations!

}


}



