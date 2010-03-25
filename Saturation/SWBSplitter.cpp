/**
 * @file SWBSplitter.cpp
 * Implements class SWBSplitter.
 */

#include "../Lib/DArray.hpp"
#include "../Lib/DHMap.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/IntUnionFind.hpp"

#include "../Kernel/BDD.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/InferenceStore.hpp"
#include "../Kernel/Signature.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/TermIterators.hpp"

#include "../Shell/Options.hpp"
#include "../Shell/Statistics.hpp"

#include "../Indexing/TermSharing.hpp"
#include "../Inferences/PropositionalToBDDISE.hpp"

#include "SaturationAlgorithm.hpp"

#include "SWBSplitter.hpp"

namespace Saturation
{

using namespace Lib;
using namespace Kernel;
using namespace Inferences;

/**
 * Try to split clause @b cl into components, return true if successful
 *
 * When true is returned, the clause @b cl should not be kept in the
 * run of the saturation algorithm.
 *
 * The splitted components (or the clause replacement) are added to the
 * @b SaturationAlgorithm object through the @b addNewClause function,
 * also the functions @b onParenthood and @b onClauseReduction are
 * called when appropriate.
 */
bool SWBSplitter::doSplitting(Clause* cl)
{
  CALL("SWBSplitter::doSplitting");
  ASS(cl->noSplits());

  if(!splittingAllowed(cl)) {
    return false;
  }

  unsigned clen=cl->length();
  ASS_G(clen,0);

  if(clen<=1) {
    return handleNoSplit(cl);
  }

  //Master literal of an variable is the literal
  //with lowest index, in which it appears.
  static DHMap<unsigned, unsigned, IdentityHash> varMasters;
  varMasters.reset();
  IntUnionFind components(clen);
  //index of one literal that cannot be splitted-out, or -1 if there isn't any
  int coloredMaster=-1;

  for(unsigned i=0;i<clen;i++) {
    Literal* lit=(*cl)[i];
    if( !canSplitOut(lit) ) {
      if(coloredMaster==-1) {
	coloredMaster=i;
      } else {
	//colored literals must be in one component
	components.doUnion(coloredMaster, i);
      }
    }
    VariableIterator vit(lit);
    while(vit.hasNext()) {
      unsigned master=varMasters.findOrInsert(vit.next().var(), i);
      if(master!=i) {
	components.doUnion(master, i);
      }
    }
  }
  components.evalComponents();

  unsigned compCnt=components.getComponentCount();

  if(standAloneObligations() && compCnt>1) {

    //we will join components without literals that cannot stand alone
    //to ones that have such (an example of a literal that cannot stand
    //alone is a negative literal when splitPositive() is true)

    IntUnionFind::ComponentIterator cit(components);

    int someCompEl=-1;
    bool someCompOK=false;
    while(cit.hasNext()) {
      IntUnionFind::ElementIterator elit=cit.next();

      int compEl=elit.next();
      if(someCompEl==-1) {
	someCompEl=compEl;
      }
      bool saok=false; //ok to stand alone
      for(;;) {
	if(canStandAlone((*cl)[compEl])) {
	  saok=true;
	  break;
	}
	if(!elit.hasNext()) {
	  break;
	}
	compEl=elit.next();
      }
      if(!saok || !someCompOK) {
	components.doUnion(compEl, someCompEl);
	if(saok) {
	  someCompOK=true;
	}
      }
    }

    //recompute the components
    components.evalComponents();
    compCnt=components.getComponentCount();
  }

  if(compCnt==1) {
    return handleNoSplit(cl);
  }

  env.statistics->splittedClauses++;
  env.statistics->splittedComponents+=compCnt;

  static DArray<Literal*> lits;
  lits.ensure(clen);
  unsigned litsNextAvail=0;

  static DArray<CompRec> comps;
  comps.ensure(compCnt);
  unsigned compi=0;

  int masterIndex=-1;

  IntUnionFind::ComponentIterator cit(components);
  ASS(cit.hasNext());
  while(cit.hasNext()) {
    IntUnionFind::ElementIterator elit=cit.next();

    bool master=false;
    Literal** first=&lits[litsNextAvail];
    int compLen=0;

    while(elit.hasNext()) {
      int litIndex=elit.next();
      lits[litsNextAvail++]=(*cl)[litIndex];
      compLen++;
      if(litIndex==coloredMaster) {
	master=true;
      }
    }

    if(master) {
      masterIndex=compi;
    }
    comps[compi++]=CompRec(first, compLen);
  }
  ASS_EQ(compi,compCnt);
  ASS_EQ(litsNextAvail,clen);
  bool haveMaster=masterIndex!=-1;
  if(haveMaster) {
    swap(comps[0], comps[masterIndex]);
  }

  buildAndInsertComponents(cl, comps.array(), compCnt, haveMaster);
  return true;
}

/**
 * Return true if @b lit cannot be split out of a clause
 */
bool SWBSplitter::canSplitOut(Literal* lit)
{
  return lit->color()==COLOR_TRANSPARENT &&
    (!env.options->showSymbolElimination() || lit->skip()) &&
    !env.signature->getPredicate(lit->functor())->cfName();
}

/**
 * Return false for literals that cannot have a splitting component
 * consisting only of them
 */
bool SWBSplitter::canStandAlone(Literal* lit)
{
  if(lit->isNegative() && splitPositive()) {
    return false;
  }
  return true;
}

/**
 * Return true if there are can be literals that cannot stand alone
 */
bool SWBSplitter::standAloneObligations()
{
  return splitPositive();
}

}
