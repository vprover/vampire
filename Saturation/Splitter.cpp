/**
 * @file Splitter.cpp
 * Implements class Splitter.
 */

#include "../Lib/DHMap.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/IntUnionFind.hpp"
#include "../Kernel/BDD.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/Term.hpp"
#include "../Shell/Statistics.hpp"

#include "Splitter.hpp"

namespace Saturation
{

using namespace Lib;
using namespace Kernel;


void Splitter::doSplitting(Clause* cl, ClauseIterator& newComponents,
	ClauseIterator& modifiedComponents)
{
  CALL("Splitter::doSplitting");

  //TODO: record inference steps

  BDD* bdd=BDD::instance();

  int clen=cl->length();

  if(clen<=1) {
    handleNoSplit(cl, newComponents, modifiedComponents);
    return;
  }

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

  if(compCnt==1) {
    handleNoSplit(cl, newComponents, modifiedComponents);
    return;
  }

  env.statistics->splittedClauses++;
  env.statistics->splittedComponents+=compCnt;

//  cout<<"####Split####\n";
//  cout<<(*cl)<<endl;
//  cout<<"vvv Into vvv\n";

  ClauseList* newComponentLst=0;
  ClauseList* modifiedComponentLst=0;
  static Stack<int> componentNames(16);

  static Stack<Literal*> lits(16);

  IntUnionFind::ComponentIterator cit(components);
  bool last;
  ASS(cit.hasNext());
  while(cit.hasNext()) {

    IntUnionFind::ElementIterator elit=cit.next();
    last=!cit.hasNext();

    lits.reset();

    while(elit.hasNext()) {
      int litIndex=elit.next();
      lits.push((*cl)[litIndex]);
    }
    int compLen=lits.size();

    Clause* comp;
    int compName=-1;
    bool newlyCreated=false;
    ClauseIterator variants=_variantIndex.retrieveVariants(lits.begin(), compLen);
    if(variants.hasNext()) {
      comp=variants.next();

      if(variants.hasNext()) {
	cout<<compName<<":  "<<(*comp)<<endl;
	while(variants.hasNext()) {
	  comp=variants.next();
	  cout<<_clauseNames.findOrInsert(comp,-1)<<":  "<<(*comp)<<endl;
	}
//	cout<<"------";
//	cout<<treeStr;
	ASSERTION_VIOLATION;
      }

      ASS(!variants.hasNext());
      if(!_clauseNames.find(comp, compName)) {
	compName=-1;
      }
    } else {
      env.statistics->uniqueComponents++;
      Inference* inf=new Inference(Inference::SPLITTING_COMPONENT);
      Unit::InputType inpType = cl->inputType();
      comp = new(compLen) Clause(compLen, inpType, inf);
      for(int i=0;i<compLen;i++) {
	(*comp)[i]=lits.pop();
      }

      _variantIndex.insert(comp);

      comp->setProp(bdd->getTrue());

      ClauseList::push(comp, newComponentLst);
      newlyCreated=true;
    }

    if(last) {
      BDDNode* newProp=cl->prop();
      if(!newProp) {
	ASSERTION_VIOLATION;
	newProp=bdd->getFalse();
      }
      while(componentNames.isNonEmpty()) {
	newProp=bdd->disjunction(newProp, bdd->getAtomic(componentNames.pop(), true));
      }
      BDDNode* oldProp=comp->prop();
      comp->setProp( bdd->conjunction(oldProp, newProp) );
      if(oldProp!=comp->prop()) {
	ClauseList::push(comp, modifiedComponentLst);
      }
    } else {
      if(compName==-1) {
	compName=bdd->getNewVar();
	comp->setProp(bdd->conjunction(comp->prop(), bdd->getAtomic(compName, false)));
	ALWAYS(_clauseNames.insert(comp, compName));
	if(!newlyCreated) {
	  ClauseList::push(comp, modifiedComponentLst);
	}
      }
      componentNames.push(compName);
    }
//    cout<<(*comp)<<endl;

  }
  ASS(last);


  newComponents=getPersistentIterator(ClauseList::Iterator(newComponentLst));
  modifiedComponents=getPersistentIterator(ClauseList::Iterator(modifiedComponentLst));

  newComponentLst->destroy();
  modifiedComponentLst->destroy();
}

void Splitter::handleNoSplit(Clause* cl, ClauseIterator& newComponents,
	ClauseIterator& modifiedComponents)
{
  BDD* bdd=BDD::instance();

  newComponents=ClauseIterator::getEmpty();
  modifiedComponents=ClauseIterator::getEmpty();

  ClauseIterator variants=_variantIndex.retrieveVariants(cl->literals(), cl->length());
  if(variants.hasNext()) {
    Clause* comp=variants.next();
    ASS(!variants.hasNext());

    BDDNode* oldProp=comp->prop();
    comp->setProp( bdd->conjunction(oldProp, cl->prop()) );

    if( comp->isEmpty() && bdd->isFalse(comp->prop()) ) {
      cl->setProp(comp->prop());
      newComponents=pvi( getSingletonIterator(cl) );
    } else if(oldProp!=comp->prop()) {
      modifiedComponents=pvi( getSingletonIterator(comp) );
    }
  } else {
    _variantIndex.insert(cl);
    newComponents=pvi( getSingletonIterator(cl) );
  }
}


}
