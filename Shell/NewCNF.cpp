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

  ASS(_queue.isEmpty());
  _queue.push_back(f);

  SPGenClause topLevelSingleton = SPGenClause(new GenClause(f));

  ASS(_genClauses.empty());
  _genClauses.push_front(topLevelSingleton); //push_front, so that begin() "points" here

  OccInfo occInfo;
  occInfo.posCnt++;
  SPGenClauseLookupList::push(make_pair(topLevelSingleton,_genClauses.begin()),occInfo.posOccs);

  ASS(_occurences.isEmpty());
  ALWAYS(_occurences.insert(f,occInfo));

  processAll();

  createClauses(output);
}

void NewCNF::processAndOr(Formula* g, OccInfo& occInfo)
{
  CALL("NewCNF::processAndOr");

  ASS(g->connective() == OR || g->connective() == AND);

  FormulaList* args = g->args();
  unsigned argLen = args->length();

  // update the queue and the occurrences for sub-formulas here
  {
    FormulaList::Iterator it(args);
    while (it.hasNext()) {
      Formula* arg = it.next();
      _queue.push_back(arg);
      ALWAYS(_occurences.insert(arg,OccInfo()));
    }
  }

  // start expanding for g

  SPGenClauseLookupList* toLinarize;   // the positive OR and negative AND
  SPGenClauseLookupList* toDistribute; // the negative AND and positive OR
  bool linierizePositively; // == !distributeNegatively

  if (g->connective() == OR) {
    toLinarize = occInfo.posOccs;
    toDistribute = occInfo.negOccs;
    linierizePositively = true;
  } else {
    toLinarize = occInfo.negOccs;
    toDistribute = occInfo.posOccs;
    linierizePositively = false;
  }

  // process toLinarize

  while (SPGenClauseLookupList::isNonEmpty(toLinarize)) {
    SPGenClauseLookup gcl = SPGenClauseLookupList::pop(toLinarize);

    SPGenClause gcOrig = gcl.first;
    if (!gcOrig->valid) {
      continue;
    }

    gcOrig->valid = false;
    GenClauses::iterator gci = gcl.second;
    _genClauses.erase(gci);

    DArray<GenLit>& litsOrig = gcOrig->lits;
    unsigned lenOrig = litsOrig.size();

    SPGenClause gcNew = SPGenClause(new GenClause(lenOrig+argLen-1));
    _genClauses.push_front(gcNew);

    DArray<GenLit>& litsNew = gcNew->lits;
    unsigned idx = 0;

    for (unsigned i = 0; i < lenOrig; i++) {
      GenLit gl = litsOrig[i];

      if (gl.first == g) { // there should be only one such occurrence in gcOrig
        ASS(gl.second == linierizePositively);

        // insert arguments instead of g here (and update occurrences)
        FormulaList::Iterator it(args);
        while (it.hasNext()) {
          Formula* arg = it.next();

          litsNew[idx++] = make_pair(arg,linierizePositively);

          OccInfo& occInfo = _occurences.get(arg);

          SPGenClauseLookupList::push(make_pair(gcNew,_genClauses.begin()),occInfo.occs(linierizePositively));

          occInfo.cnt(linierizePositively) += 1;
        }

      } else {
        litsNew[idx++] = gl;

        OccInfo& occInfo = _occurences.get(gl.first);

        SPGenClauseLookupList::push(make_pair(gcNew,_genClauses.begin()),occInfo.occs(gl.second));

        // the number of occurrences stays intact
      }
    }
  }

  // process toDistribute

  while (SPGenClauseLookupList::isNonEmpty(toDistribute)) {
    SPGenClauseLookup gcl = SPGenClauseLookupList::pop(toDistribute);

    SPGenClause gcOrig = gcl.first;
    if (!gcOrig->valid) {
      continue;
    }

    gcOrig->valid = false;
    GenClauses::iterator gci = gcl.second;
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

        if (gl.first == g) { // there should be only one such occurrence in gcOrig
          ASS(gl.second == !linierizePositively);

          litsNew[i] = make_pair(arg,!linierizePositively);

          OccInfo& occInfo = _occurences.get(arg);
          SPGenClauseLookupList::push(make_pair(gcNew,_genClauses.begin()),occInfo.occs(!linierizePositively));
          occInfo.cnt(!linierizePositively) += 1;
        } else {
          litsNew[i] = gl;

          OccInfo& occInfo = _occurences.get(gl.first);
          SPGenClauseLookupList::push(make_pair(gcNew,_genClauses.begin()),occInfo.occs(gl.second));
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

  // update the queue and the occurrences for sub-formulas here

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

      SPGenClause gcOrig = gcl.first;
      if (!gcOrig->valid) {
        continue;
      }

      gcOrig->valid = false;
      GenClauses::iterator gci = gcl.second;
      _genClauses.erase(gci);

      DArray<GenLit>& litsOrig = gcOrig->lits;
      unsigned lenOrig = litsOrig.size();

      SPGenClause gcNew1 = SPGenClause(new GenClause(lenOrig+1));
      _genClauses.push_front(gcNew1);
      SPGenClauseLookup gclNew1 = make_pair(gcNew1,_genClauses.begin());

      SPGenClause gcNew2 = SPGenClause(new GenClause(lenOrig+1));
      _genClauses.push_front(gcNew2);
      SPGenClauseLookup gclNew2 = make_pair(gcNew2,_genClauses.begin());

      DArray<GenLit>& litsNew1 = gcNew1->lits;
      DArray<GenLit>& litsNew2 = gcNew2->lits;
      unsigned idx = 0;

      for (unsigned i = 0; i < lenOrig; i++) {
        GenLit gl = litsOrig[i];

        if (gl.first == g) { // there should be only one such occurrence in gcOrig
          ASS(gl.second == (g->connective() == IFF));

          litsNew1[idx] = make_pair(left,false);
          SPGenClauseLookupList::push(gclNew1,leftOccInfo.occs(false));
          leftOccInfo.cnt(false) += 1;

          litsNew2[idx] = make_pair(left,true);
          SPGenClauseLookupList::push(gclNew2,leftOccInfo.occs(true));
          leftOccInfo.cnt(true) += 1;

          idx++;

          bool secondIn1st = !flip;
          litsNew1[idx] = make_pair(right,secondIn1st);
          SPGenClauseLookupList::push(gclNew1,rightOccInfo.occs(secondIn1st));
          rightOccInfo.cnt(secondIn1st) += 1;

          bool secondIn2nd = flip;
          litsNew2[idx] = make_pair(right,secondIn2nd);
          SPGenClauseLookupList::push(gclNew2,rightOccInfo.occs(secondIn2nd));
          rightOccInfo.cnt(secondIn2nd) += 1;

          idx++;
        } else {
          litsNew1[idx] = gl;
          litsNew2[idx] = gl;
          idx++;

          OccInfo& occInfo = _occurences.get(gl.first);
          SPGenClauseLookupList::push(gclNew1,occInfo.occs(gl.second));
          SPGenClauseLookupList::push(gclNew2,occInfo.occs(gl.second));

          occInfo.cnt(gl.first) += 1; // just +1, for it was there already once
        }
      }
    }
  }
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
        // flip polarity of negative occurrences

        // apply skolemising substitution

        // don't do it in-place!

        // TODO: clear occInfo to release stale ones

        break;

      case AND:
      case OR:
        processAndOr(g,occInfo);
        break;

      case IFF:
      case XOR:


      // keep inserting subformulas in the queue !

      // keep emptying occInfo for the current g


      case TRUE:

      case FALSE:

      default:
        ASSERTION_VIOLATION;
    }


  }

  // produce clauses out of the generalized ones (while are now flat)
  // careful about double negations!



}

void NewCNF::createClauses(Lib::Stack<Kernel::Clause*>& output)
{
  CALL("NewCNF::createClauses");


}


}



