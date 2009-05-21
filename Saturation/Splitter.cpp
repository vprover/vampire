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

#define REPORT_SPLITS 0

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

#if REPORT_SPLITS
  cout<<"####Split####\n";
  cout<<(*cl)<<endl;
  cout<<"vvv Into vvv\n";
#endif

  static Stack<Clause*> unnamedComponentStack(16);
  static Stack<Clause*> newComponentStack(16);
  unnamedComponentStack.reset();
  newComponentStack.reset();

  BDDNode* newMasterProp=cl->prop();

  static Stack<Literal*> lits(16);

  IntUnionFind::ComponentIterator cit(components);
  Clause* masterComp=0;
  ASS(cit.hasNext());
  while(cit.hasNext()) {

    IntUnionFind::ElementIterator elit=cit.next();
    bool last=!cit.hasNext();

    lits.reset();

    while(elit.hasNext()) {
      int litIndex=elit.next();
      lits.push((*cl)[litIndex]);
    }
    int compLen=lits.size();

    Clause* comp;
    ClauseIterator variants=_variantIndex.retrieveVariants(lits.begin(), compLen);
    if(variants.hasNext()) {
      comp=variants.next();

      ASS(!variants.hasNext());
      int compName;
      if(_clauseNames.find(comp, compName)) {
	if(last && newComponentStack.isEmpty() && unnamedComponentStack.isEmpty()) {
	  masterComp=comp;
	} else {
	  newMasterProp=bdd->disjunction(newMasterProp, bdd->getAtomic(compName, true));
#if REPORT_SPLITS
	  cout<<compName<<": "<<(*comp)<<endl;
#endif
	  if(bdd->isTrue(newMasterProp)) {
	    //the propositional part of cl is true, so there is no point in adding it
	    newComponents=ClauseIterator::getEmpty();
	    modifiedComponents=ClauseIterator::getEmpty();
	    return;
	  }
	}
      } else {
	unnamedComponentStack.push(comp);
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

      newComponentStack.push(comp);
    }
  }

  newComponents=getPersistentIterator(Stack<Clause*>::Iterator(newComponentStack));

  bool masterNew=false;
  if(newComponentStack.isNonEmpty()) {
    ASS(!masterComp);
    masterNew=true;
    masterComp=newComponentStack.pop();
  } else if(unnamedComponentStack.isNonEmpty()) {
    ASS(!masterComp);
    masterComp=unnamedComponentStack.pop();
  } else {
    ASS(masterComp);
  }


  ClauseIterator unnamedIt=pvi( getConcatenatedIterator(
	  Stack<Clause*>::Iterator(newComponentStack),
	  Stack<Clause*>::Iterator(unnamedComponentStack)) );
  while(unnamedIt.hasNext()) {
    Clause* comp=unnamedIt.next();
    int compName=bdd->getNewVar();

    if(_clauseNames.insert(comp, compName)) {
      //The same component can appear multiple times.
      //We detect the harmful cases here as attempts to name
      //a component multiple times.
      comp->setProp(bdd->conjunction(comp->prop(), bdd->getAtomic(compName, false)));
      newMasterProp=bdd->disjunction(newMasterProp, bdd->getAtomic(compName, true));
#if REPORT_SPLITS
      cout<<compName<<": "<<(*comp)<<endl;
#endif
    }
  }

  ASS(!bdd->isTrue(newMasterProp));

  BDDNode* oldProp=masterComp->prop();
  masterComp->setProp( bdd->conjunction(oldProp, newMasterProp) );
  ASS(!bdd->isTrue(masterComp->prop()));

#if REPORT_SPLITS
  cout<<(*masterComp)<<endl;
#endif

  if(oldProp!=masterComp->prop() && !masterNew) {
    modifiedComponents=getPersistentIterator(getConcatenatedIterator(
		  getSingletonIterator(masterComp),
		  Stack<Clause*>::Iterator(unnamedComponentStack)) );
  } else {
    modifiedComponents=getPersistentIterator(
		  Stack<Clause*>::Iterator(unnamedComponentStack) );
  }

#if REPORT_SPLITS
  cout<<"^^^^^^^^^^^^\n";
#endif

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

    if(variants.hasNext()) {
	cout<<(*cl)<<endl;
	cout<<_clauseNames.findOrInsert(comp,-1)<<":  "<<(*comp)<<endl;
	while(variants.hasNext()) {
	  comp=variants.next();
	  cout<<_clauseNames.findOrInsert(comp,-1)<<":  "<<(*comp)<<endl;
	}
//	cout<<"------";
//	cout<<treeStr;
	ASSERTION_VIOLATION;
    }

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
    env.statistics->uniqueComponents++;
    _variantIndex.insert(cl);
    newComponents=pvi( getSingletonIterator(cl) );
  }
}


}
