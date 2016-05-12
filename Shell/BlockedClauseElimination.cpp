/**
 * @file BlockedClauseElimination.cpp
 * Implements class Blocked Clause Elimination.
 */

#include "BlockedClauseElimination.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/RobSubstitution.hpp"

#include "Lib/SmartPtr.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/BinaryHeap.hpp"

#include "Shell/Statistics.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;

void BlockedClauseElimination::apply(Problem& prb)
{
  CALL("BlockedClauseElimination::apply(Problem&)");

  bool modified = false;

  if (prb.hasEquality()) {
    ASSERTION_VIOLATION;
  } else {
    DArray<Stack<Candidate*>> positive(env.signature->predicates());
    DArray<Stack<Candidate*>> negative(env.signature->predicates());

    Stack<ClWrapper*> wrappers; // just to delete easily in the end

    // cout << "Entering the non-equality case" << endl;

    // put the clauses into the index
    UnitList::Iterator uit(prb.units());
    while(uit.hasNext()) {
      Clause* cl=static_cast<Clause*>(uit.next());
      ASS(cl->isClause());

      ClWrapper* clw = new ClWrapper(cl);
      wrappers.push(clw);

      for(unsigned i=0; i<cl->length(); i++) {
        Literal* lit = (*cl)[i];
        unsigned pred = lit->functor();
        (lit->isPositive() ? positive : negative)[pred].push(new Candidate {clw,i,0,0});
      }
    }

    // cout << "Clauses indexed" << endl;

    typedef BinaryHeap<Candidate*, CandidateComparator> BlockClauseCheckPriorityQueue;
    BlockClauseCheckPriorityQueue queue;

    for (bool pos : {false, true}) {
      DArray<Stack<Candidate*>>& one   = pos ? positive : negative;
      DArray<Stack<Candidate*>>& other = pos ? negative : positive;

      for (unsigned pred = 0; pred < one.size(); pred++) {
        Stack<Candidate*>& predsCandidates = one[pred];
        unsigned predsRemaining = other[pred].size();
        for (unsigned i = 0; i < predsCandidates.size(); i++) {
          Candidate* cand = predsCandidates[i];
          cand->weight = predsRemaining;
          queue.insert(cand);
        }
      }
    }

    // cout << "Queue initialized" << endl;

    while (!queue.isEmpty()) {
      Candidate* cand = queue.pop();
      ClWrapper* clw = cand->clw;

      if (clw->blocked) {
        continue;
      }

      // clause still undecided
      Clause* cl = clw->cl;
      Literal* lit = (*cl)[cand->litIdx];
      unsigned pred = lit->functor();
      Stack<Candidate*>& partners = (lit->isPositive() ? negative : positive)[pred];

      for (unsigned i = cand->contFrom; i < partners.size(); i++) {
        Candidate* partner = partners[i];
        ClWrapper* pclw = partner->clw;
        Clause* pcl = pclw->cl;

        if (pclw->blocked) {
          continue;
        }

        if (!resolvesToTautology(cl,lit,pcl,(*pcl)[partner->litIdx])) {
          // cand does not work, because of partner; need to wait for partner to die
          cand->contFrom = i+1;
          cand->weight = partners.size() - cand->contFrom;
          pclw->toResurrect.push(cand);
          goto next_candidate;
        }
      }

      // resolves to tautology with all partners -- blocked!
      // cout << "Blocked clause[" << cand->litIdx << "]: " << cl->toString() << endl;

      env.statistics->blockedClauses++;
      modified = true;

      clw->blocked = true;
      for (unsigned i = 0; i< clw->toResurrect.size(); i++) {
        queue.insert(clw->toResurrect[i]);
      }
      clw->toResurrect.reset();

      next_candidate: ;
    }

    // delete candidates:
    for (bool pos : {false, true}) {
      DArray<Stack<Candidate*>> & one   = pos ? positive : negative;

      for (unsigned pred = 0; pred < one.size(); pred++) {
        Stack<Candidate*>& predsCandidates = one[pred];
        for (unsigned i = 0; i < predsCandidates.size(); i++) {
          delete predsCandidates[i];
        }
      }
    }

    // delete wrappers and update units in prob, if there were any blockings
    UnitList* res=0;

    Stack<ClWrapper*>::Iterator it(wrappers);
    while (it.hasNext()) {
      ClWrapper* clw = it.next();
      if (modified && !clw->blocked) {
        UnitList::push(clw->cl, res);
      }
      delete clw;
    }

    if (modified) {
      prb.units() = res;
    }
  }

  if(modified) {
    prb.invalidateProperty();
  }
}

bool BlockedClauseElimination::resolvesToTautology(Clause* cl, Literal* lit, Clause* pcl, Literal* plit)
{
  CALL("BlockedClauseElimination::resolvesToTautology");

  static RobSubstitution subst;
  subst.reset();
  if(!subst.unifyArgs(lit,0,plit,1)) {
    return true; // since they don't resolve
  }

  static DHSet<Literal*> lits;
  lits.reset();

  for (unsigned i = 0; i < cl->length(); i++) {
    Literal* curlit = (*cl)[i];
    if (curlit != lit) {
      Literal* scurlit = subst.apply(curlit,0);

      Literal* opscurlit = Literal::complementaryLiteral(scurlit);

      if (lits.find(opscurlit)) {
        return true;
      }
      lits.insert(scurlit);
    }
  }

  for (unsigned i = 0; i < pcl->length(); i++) {
    Literal* curlit = (*pcl)[i];
    if (curlit != plit) {
      Literal* scurlit = subst.apply(curlit,1);

      Literal* opscurlit = Literal::complementaryLiteral(scurlit);

      if (lits.find(opscurlit)) {
        return true;
      }
      lits.insert(scurlit);
    }
  }

  return false;
}



}
