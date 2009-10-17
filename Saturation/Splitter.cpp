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
#include "../Kernel/InferenceStore.hpp"
#include "../Kernel/Signature.hpp"
#include "../Kernel/Term.hpp"
#include "../Shell/Options.hpp"
#include "../Shell/Statistics.hpp"
#include "../Inferences/PropositionalToBDDISE.hpp"

#include "Splitter.hpp"

namespace Saturation
{

using namespace Lib;
using namespace Kernel;
using namespace Inferences;

#define REPORT_SPLITS 0

/**
 * Split clause @b cl into components. Return iterator that yields
 * new and modified components.
 *
 * A modification of a component means a change of its propositional
 * part.
 */
ClauseIterator Splitter::doSplitting(Clause* cl)
{
  CALL("Splitter::doSplitting");

  BDD* bdd=BDD::instance();

  int clen=cl->length();
  ASS_G(clen,0);

  if(clen<=1) {
    return handleNoSplit(cl);
  }

  //Master literal of an variable is the literal
  //with lowest index, in which it appears.
  static DHMap<unsigned, int, IdentityHash> varMasters;
  varMasters.reset();
  IntUnionFind components(clen);
  //index of one literal that cannot be splitted-out, or -1 if there isn't any
  int coloredMaster=-1;

  if(clen>1) {
    for(int i=0;i<clen;i++) {
      Literal* lit=(*cl)[i];
      if( !canSplitOut(lit) ) {
	if(coloredMaster==-1) {
	  coloredMaster=i;
	} else {
	  //colored literals must be in one component
	  components.doUnion(coloredMaster, i);
	}
      }
      Term::VariableIterator vit(lit);
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
    return handleNoSplit(cl);
  }

  env.statistics->splittedClauses++;
  env.statistics->splittedComponents+=compCnt;

  InferenceStore::SplittingRecord* srec=new InferenceStore::SplittingRecord(cl);
  static Stack<Clause*> masterPremises;
  masterPremises.reset();

#if REPORT_SPLITS
  cout<<"####Split####\n";
  cout<<(*cl)<<endl;
  cout<<"vvv Into vvv\n";
#endif

  static Stack<Clause*> unnamedComponentStack(16);
  unnamedComponentStack.reset();

  BDDNode* newMasterProp=cl->prop();
  masterPremises.push(cl);

  static Stack<Literal*> lits(16);

  int remainingComps=compCnt;

  IntUnionFind::ComponentIterator cit(components);
  Clause* masterComp=0;
  ASS(cit.hasNext());
  while(cit.hasNext()) {
    IntUnionFind::ElementIterator elit=cit.next();

    lits.reset();

    bool colorComponent=false;

    while(elit.hasNext()) {
      int litIndex=elit.next();
      lits.push((*cl)[litIndex]);
      if(litIndex==coloredMaster) {
	colorComponent=true;
      }
    }
    int compLen=lits.size();

    //no propositional literals that can be bddized should make it here
    ASS(compLen!=1 || !PropositionalToBDDISE::canBddize(lits.top()))
    ASS(!colorComponent | masterComp==0);

    remainingComps--;

    int compName;
    bool compNew;
    Clause* comp=getComponent(cl, lits.begin(), compLen, compName, compNew);
    if(compName) {
      ASS(!colorComponent); //colored components don't have names
      if(!remainingComps && !masterComp && unnamedComponentStack.isEmpty()) {
	//there's no component left and we still haven't found a master component
	ASS_EQ(masterComp, 0);
	masterComp=comp;
      } else {
	newMasterProp=bdd->disjunction(newMasterProp, bdd->getAtomic(compName, true));
#if REPORT_SPLITS
	cout<<compName<<": "<<(*comp)<<endl;
#endif
	if(bdd->isTrue(newMasterProp)) {
	  //the propositional part of the master component is true only
	  //due to already named components, so there's no point in adding
	  //any clause
	  return ClauseIterator::getEmpty();
	}
	masterPremises.push(comp);
	srec->namedComps.push(make_pair(compName, comp));
      }
    }
    else {
      if(colorComponent || (!coloredMaster==-1 && !masterComp && compNew) ) {
	ASS_EQ(masterComp, 0);
	masterComp=comp;
      } else {
	unnamedComponentStack.push(comp);
      }
    }
    ASS(!colorComponent | masterComp!=0);
  }

  if(!masterComp) {
    ASS(unnamedComponentStack.isNonEmpty());
    masterComp=unnamedComponentStack.pop();
  }


  Stack<Clause*>::Iterator unnamedIt(unnamedComponentStack);
  while(unnamedIt.hasNext()) {
    Clause* comp=unnamedIt.next();
    if(comp==masterComp) {
      //The same component can appear multiple times, here
      //we catch cases when the master component is unnamed
      //and appears more than once.
      continue;
    }
    int compName=bdd->getNewVar();

    if(_clauseNames.insert(comp, compName)) {
      //The same component can appear multiple times.
      //We detect the harmful cases here as attempts to name
      //a component multiple times.
      BDDNode* oldCompProp=comp->prop();
      BDDNode* newCompProp=bdd->conjunction(oldCompProp, bdd->getAtomic(compName, false));
      if(newCompProp!=oldCompProp) {
	comp->setProp(newCompProp);
	InferenceStore::instance()->recordPropAlter(comp, oldCompProp, newCompProp, Inference::CLAUSE_NAMING);
      }
      newMasterProp=bdd->disjunction(newMasterProp, bdd->getAtomic(compName, true));
      masterPremises.push(comp);
      srec->namedComps.push(make_pair(compName, comp));

      if(env.options->showDefinitions()) {
        env.out << "Definition: " << BDD::instance()->getPropositionalPredicateName(compName)
  	    << " <=> (" << comp->nonPropToString() << ")" << endl;
      }

#if REPORT_SPLITS
      cout<<'n'<<compName<<": "<<(*comp)<<endl;
#endif
    }
  }
  ASS(!bdd->isTrue(newMasterProp));

  InferenceStore::ClauseSpec splittedMCompCS=InferenceStore::getClauseSpec(masterComp, newMasterProp);

  srec->result=splittedMCompCS;
  InferenceStore::instance()->recordSplitting(srec, masterPremises.size(),
	  masterPremises.begin());

  BDDNode* oldProp=masterComp->prop();
  masterComp->setProp( bdd->conjunction(oldProp, newMasterProp) );
  if(oldProp!=masterComp->prop() && newMasterProp!=masterComp->prop()) {
    InferenceStore::instance()->recordMerge(masterComp, oldProp, newMasterProp, masterComp->prop());
  }

  ASS(!bdd->isTrue(masterComp->prop()));

#if REPORT_SPLITS
  cout<<(*masterComp)<<endl;
#endif

  if(oldProp!=masterComp->prop()) {
    return getPersistentIterator(getConcatenatedIterator(
	    getSingletonIterator(masterComp),
	    Stack<Clause*>::Iterator(unnamedComponentStack)) );
  } else {
    return getPersistentIterator(
	    Stack<Clause*>::Iterator(unnamedComponentStack) );
  }

#if REPORT_SPLITS
  cout<<"^^^^^^^^^^^^\n";
#endif

}

bool Splitter::canSplitOut(Literal* lit)
{
  return lit->color()==COLOR_TRANSPARENT &&
    (!env.options->showSymbolElimination() || lit->skip());
}

/**
 * Return true if literal @b l is bipolar
 *
 * A literal is bipolar if the same name can be used both for its
 * positive and negative occurence.
 */
bool Splitter::isBipolar(Literal* lit)
{
  return lit->ground();
}


//void Splitter::getPropPredName(Literal* lit, int& name, Clause*& premise, bool& newPremise)
//{
//  CALL("Splitter::getPropPredName");
//  ASS_EQ(lit->arity(), 0);
//
//  unsigned pred=lit->functor();
//  int* pname;
//  if(_propPredNames.getValuePtr(pred, pname)) {
//    *pname=BDD::instance()->getNewVar( pred );
//
//    if(env.options->showDefinitions()) {
//      env.out << "Definition: " << BDD::instance()->getPropositionalPredicateName(*pname)
//	    << " <=> " << env.signature->predicateName(pred) << endl;
//    }
//  }
//  name=*pname;
//
//  Clause** ppremise;
//  if(lit->isPositive()) {
//    _propPredPosNamePremises.getValuePtr(pred, ppremise, 0);
//  } else {
//    _propPredNegNamePremises.getValuePtr(pred, ppremise, 0);
//  }
//  newPremise=*ppremise;
//  if(!*ppremise) {
//    Clause* cl=new(1) Clause(1,Clause::AXIOM,new Inference(Inference::CLAUSE_NAMING));
//    (*cl)[0]=lit;
//    cl->setProp( BDD::instance()->getAtomic(name, lit->isNegative()) );
//    InferenceStore::instance()->recordNonPropInference(cl);
//    *ppremise=cl;
//  }
//  premise=*ppremise;
//}

/**
 * Return component of @b cl that contains literals in array @b lits
 * (that has length @b compLen). If the component has a name,
 * assign it to @b name, otherwise assigh 0 to @b name.
 * Assign @b true to @b newComponent iff the component was
 * newly added to the component index.
 */
Clause* Splitter::getComponent(Clause* cl, Literal** lits, unsigned compLen, int& name, bool& newComponent)
{
  Clause* comp;
  ClauseIterator variants=_variantIndex.retrieveVariants(lits, compLen);
  newComponent=!variants.hasNext();
  if(!newComponent) {
    comp=variants.next();

    ASS(!variants.hasNext());
    if(!_clauseNames.find(comp, name)) {
      name=0;
    }
#if VDEBUG
    else {
      ASS_NEQ(name,0);
    }
#endif
  } else {
    name=0;

    env.statistics->uniqueComponents++;
    Inference* inf=new Inference(Inference::TAUTOLOGY_INTRODUCTION);
    Unit::InputType inpType = cl->inputType();
    comp = new(compLen) Clause(compLen, inpType, inf);
    for(unsigned i=0;i<compLen;i++) {
      (*comp)[i]=lits[i];
    }

    {
      TimeCounter tc(TC_SPLITTING_COMPONENT_INDEX_MAINTENANCE);

      _variantIndex.insert(comp);
    }

    comp->setProp(BDD::instance()->getTrue());
    InferenceStore::instance()->recordNonPropInference(comp);
  }
  return comp;
}

Clause* Splitter::insertIntoIndex(Clause* cl, bool& newInserted, bool& modified)
{
  CALL("Splitter::insertIntoIndex");

  BDD* bdd=BDD::instance();

  newInserted=false;
  modified=false;

  ClauseIterator variants=_variantIndex.retrieveVariants(cl->literals(), cl->length());
  if(variants.hasNext()) {
    Clause* comp=variants.next();

    ASS(!variants.hasNext());

    BDDNode* oldCompProp=comp->prop();
    BDDNode* oldClProp=cl->prop();
    BDDNode* newCompProp=bdd->conjunction(oldCompProp, oldClProp);

    if(oldCompProp==newCompProp) {
      return comp;
    }

#if REPORT_SPLITS
    cout<<"----Merging----\n";
    cout<<"Clause "<<(*cl)<<" caused\n";
    cout<<(*comp)<<" to get prop. part\n";
    cout<<bdd->toString(newCompProp)<<endl;
    cout<<"^^^^^^^^^^^^^^^\n";
#endif
    comp->setProp( newCompProp );
    InferenceStore::instance()->recordMerge(comp, oldCompProp, cl, newCompProp);

    modified=true;
    return comp;

  } else {
    env.statistics->uniqueComponents++;

    {
      TimeCounter tc(TC_SPLITTING_COMPONENT_INDEX_MAINTENANCE);
      _variantIndex.insert(cl);
    }

    newInserted=true;
    return cl;
  }
}

ClauseIterator Splitter::handleNoSplit(Clause* cl)
{
  CALL("Splitter::handleNoSplit");
  ASS_G(cl->length(), 0);
  //no propositional literal that can be bddized should get here
  ASS(cl->length()!=1 || !PropositionalToBDDISE::canBddize((*cl)[0]));

  bool newInserted;
  bool modified;
  Clause* insCl=insertIntoIndex(cl, newInserted, modified);

  if(newInserted || modified) {
    return pvi( getSingletonIterator(insCl) );
  }
  else {
    return ClauseIterator::getEmpty();
  }
}


}
