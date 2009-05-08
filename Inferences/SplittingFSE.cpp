/**
 * @file SplittingFSE.cpp
 * Implements class SplittingFSE.
 */

#include "../Lib/DHMap.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/IntUnionFind.hpp"
#include "../Kernel/BDD.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/Term.hpp"
#include "../Shell/Statistics.hpp"

#include "SplittingFSE.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;

void SplittingFSE::perform(Clause* cl, bool& keep, ClauseIterator& toAdd,
	ClauseIterator& premises)
{
  CALL("SplittingFSE::perform");

  keep=true;
  toAdd=ClauseIterator::getEmpty();
  premises=ClauseIterator::getEmpty();

  int clen=cl->length();
  ASS_GE(clen,0); //no overflow
//  if(clen<=1) {
//    return;
//  }

  //Master literal of an variable is the literal
  //with lowest index, in which it appears.
  static DHMap<unsigned, int, IdentityHash> varMasters;
  varMasters.reset();
  IntUnionFind components(clen);

  if(clen>1) {
    for(int i=0;i<clen;i++) {
      Term::VariableIterator vit((*cl)[i]);
      while(vit.hasNext()) {
	int master=varMasters.findOrInsert(vit.next().var(), i);
	if(master!=i) {
	  components.doUnion(master, i);
	}
      }
    }
  }
  components.finish();

  int compCnt=components.getComponentCount();

  if(compCnt!=1) {
    env.statistics->splittedClauses++;
    env.statistics->splittedComponents+=compCnt;
  }

  ClauseList* toAddLst=0;
  static Stack<int> componentNames(16);

  static Stack<Literal*> lits(16);

  BDD* bdd=BDD::instance();
//  static DArray<int> clSizes;
//  clSizes.ensure(compCnt);
//
//  int compIndex=0;
  IntUnionFind::ComponentIterator cit(components);
  while(cit.hasNext()) {

    IntUnionFind::ElementIterator elit=cit.next();
    bool last=cit.hasNext();

    lits.reset();

    while(elit.hasNext()) {
      int litIndex=elit.next();
      lits.push((*cl)[litIndex]);
    }
    int compLen=lits.size();

    Clause* comp=0;
    int compName;
    ClauseIterator variants=_variantIndex.retrieveVariants(lits.begin(), compLen);
    if(variants.hasNext()) {
      comp=variants.next();
      compName=_clauseNames.get(comp);
      ASS(!variants.hasNext()); //TODO: this fails e.g. on ALG214+1
    }

    if(comp==0) {
      env.statistics->uniqueComponents++;
      Inference* inf=new Inference(Inference::SPLITTING_COMPONENT);
      Unit::InputType inpType = cl->inputType();
      comp = new(compLen) Clause(compLen, inpType, inf);
      for(int i=0;i<compLen;i++) {
	(*comp)[i]=lits.pop();
      }

      compName=bdd->getNewVar();
      comp->setProp(bdd->getAtomic(compName, false));
      _variantIndex.insert(comp);
      ALWAYS(_clauseNames.insert(comp, compName));
    }

    if(last) {
      BDDNode* newProp=cl->prop();
      if(!newProp) {
	newProp=bdd->getFalse();
      }
      while(componentNames.isNonEmpty()) {
	newProp=bdd->disjunction(newProp, bdd->getAtomic(componentNames.pop(), true));
      }
      comp->setProp( bdd->conjunction(comp->prop(), newProp) );
      //TODO: also alter the inference object in case we're reusing a clause
    } else {
      componentNames.push(compName);
    }

    ClauseList::push(comp, toAddLst);
  }


//  keep=false;
//  toAdd=getPersistentIterator(ClauseList::Iterator(toAddLst));
}

}
