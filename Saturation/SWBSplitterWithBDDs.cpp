/**
 * @file SWBSplitterWithBDDs.cpp
 * Implements class SWBSplitterWithBDDs.
 */

#include "Kernel/BDD.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Term.hpp"

#include "Indexing/TermSharing.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "SaturationAlgorithm.hpp"

#include "SWBSplitterWithBDDs.hpp"

namespace Saturation
{

void SWBSplitterWithBDDs::buildAndInsertComponents(Clause* cl, CompRec* comps, unsigned compCnt, bool firstIsMaster)
{
  CALL("SWBSplitterWithBDDs::buildAndInsertComponents");

#if REPORT_SPLITS
  cout<<"####Split####\n";
  cout<<(*cl)<<endl;
  cout<<"vvv Into vvv\n";
#endif

  BDD* bdd=BDD::instance();

  InferenceStore::SplittingRecord* srec=new InferenceStore::SplittingRecord(cl);

  static Stack<Clause*> unnamedComponentStack(16);
  unnamedComponentStack.reset();

  typedef pair<int, Clause*> CompNameRec;
  //The namedComponents stack contains pairs of component name and
  //the naming clause that should be added for the component to the
  //saturation algorithm.
  static Stack<CompNameRec> namedComponents(16);
  namedComponents.reset();



  int remainingComps=compCnt;


  Clause* masterComp=0;
  for(unsigned ci=0;ci<compCnt;ci++) {
    CompRec cr=comps[ci];

    remainingComps--;

    int compName;
    bool compNew;
    Clause* comp=getComponent(cl, cr, compName, compNew);
    ASS(!compNew || !compName); //new components cannot be already named

    bool isMaster= (ci==0 && firstIsMaster) || //the component has to be a master
      (!masterComp &&			       //or if we don't have a master yet,
	  (compNew ||				//we go with a new component
	   (!remainingComps && unnamedComponentStack.isEmpty())	//or with the last component if there's no other choice
	  )
      );

    if(isMaster) {
      masterComp=comp;
    }
    else if(compName) {
#if REPORT_SPLITS
      cout<<compName<<": "<<(*comp)<<endl;
#endif
      namedComponents.push(CompNameRec(compName, comp));
    }
    else {
      unnamedComponentStack.push(comp);
    }
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

    int compName=nameComponent(comp);
    if(!compName) {
      //The same component can appear multiple times.
      //If compName==0, this happened, so we skip that case.
      continue;
    }

    namedComponents.push(CompNameRec(compName, comp));


#if REPORT_SPLITS
    cout<<'n'<<compName<<": "<<(*comp)<<endl;
#endif
  }

  static Stack<Clause*> masterPremises;
  masterPremises.reset();
  masterPremises.push(cl);

  BDDNode* newMasterProp=cl->prop();

  while(namedComponents.isNonEmpty()) {
    CompNameRec cr=namedComponents.pop();
    int compName=cr.first;
    Clause* comp=cr.second;

    newMasterProp=bdd->disjunction(newMasterProp, getNameProp(compName));
    if(bdd->isTrue(newMasterProp)) {
      //the propositional part of the master component is true only
      //due to already named components, so there's no point in adding
      //any clause
      delete srec;
      _sa->onClauseReduction(cl, 0, 0);
      return;
    }
    masterPremises.push(comp);
    srec->namedComps.push(make_pair(compName, comp));
  }

  InferenceStore::UnitSpec splittedMCompCS(masterComp, newMasterProp);

  srec->result=splittedMCompCS;
  InferenceStore::instance()->recordSplitting(srec, masterPremises.size(),
	  masterPremises.begin());

  BDDNode* oldProp=masterComp->prop();
  masterComp->setProp( bdd->conjunction(oldProp, newMasterProp) );
  if(oldProp!=masterComp->prop() && newMasterProp!=masterComp->prop()) {
    InferenceStore::instance()->
      recordMerge(masterComp, oldProp, newMasterProp, masterComp->prop());
  }

  ASS(!bdd->isTrue(masterComp->prop()));

#if REPORT_SPLITS
  cout<<(*masterComp)<<endl;
  cout<<"^^^^^^^^^^^^\n";
#endif

  if(oldProp!=masterComp->prop()) {
    _sa->addNewClause(masterComp);
    _sa->onParenthood(masterComp, cl);
  }
  while(unnamedComponentStack.isNonEmpty()) {
    Clause* comp=unnamedComponentStack.pop();
    _sa->addNewClause(comp);
    _sa->onParenthood(comp, cl);
  }

  _sa->onClauseReduction(cl, 0, 0);
}


bool SWBSplitterWithBDDs::handleNoSplit(Clause* cl)
{
  CALL("SWBSplitterWithBDDs::handleNoSplit");

  return _sa->getSharing()->doSharing(cl);
}

/**
 * Return component of @b cl that contains literals in array @b lits
 * (that has length @b compLen). If the component has a name,
 * assign it to @b name, otherwise assigh 0 to @b name.
 * Assign @b true to @b newComponent iff the component was
 * newly added to the component index.
 */
Clause* SWBSplitterWithBDDs::getComponent(Clause* cl, CompRec cr, int& name, bool& newComponent)
{
  CALL("SWBSplitterWithBDDs::getComponent");

  Literal** lits=cr.lits;
  unsigned compLen=cr.len;

  Clause* comp=_sa->getSharing()->tryGet(lits,compLen);
  newComponent=!comp;
  if(comp) {
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

    Inference* inf=new Inference(Inference::TAUTOLOGY_INTRODUCTION);
    Unit::InputType inpType = cl->inputType();
    comp = new(compLen) Clause(compLen, inpType, inf);
    for(unsigned i=0;i<compLen;i++) {
      (*comp)[i]=lits[i];
    }

    comp->setAge(cl->age());
    comp->initProp(BDD::instance()->getTrue());
    InferenceStore::instance()->recordNonPropInference(comp);

    _sa->getSharing()->insertNew(comp);
  }
  return comp;
}

/**
 * Name component @b comp and return the name
 *
 * If the component @b comp is already named, return 0.
 */
int SWBSplitterWithBDDs::nameComponent(Clause* comp)
{
  CALL("SWBSplitterWithBDDs::nameComponent");

  int *pname;

  if(!_clauseNames.getValuePtr(comp, pname)) {
    //the component was already named
    return 0;
  }

  int compName=0;
  bool newlyIntroduced=true;

  if(comp->length()==1 && (*comp)[0]->ground()) {
    //both polarities of a ground component should share one name

    Literal* lit=(*comp)[0];
    Literal* opLit=env.sharing->tryGetOpposite(lit);
    //opLit==0 if the opposite counterpart of lit is not even in the sharing structure
    if(opLit && _groundNames.pop(opLit, compName)) {
      //both polatiries of the literal are now named, so it can be
      //removed from the _groundNames map (by the _groundNames.pop call above)

      //oposite polarity, so we swap the sign
      compName=-compName;
      newlyIntroduced=false;
    }
    else {
      compName = (lit->polarity()?1:-1) * BDD::instance()->getNewVar();
      env.statistics->splittingNamesIntroduced++;
      _groundNames.insert(lit, compName);
    }
  }
  else {
    compName=BDD::instance()->getNewVar();
    env.statistics->splittingNamesIntroduced++;
  }

  *pname=compName;
  BDDNode* oldCompProp=comp->prop();
  BDDNode* nameProp=BDD::instance()->getAtomic(abs(compName), compName<0);
  BDDNode* newCompProp=BDD::instance()->conjunction(oldCompProp, nameProp);
  if(newCompProp!=oldCompProp) {
    comp->setProp(newCompProp);
    InferenceStore::instance()->recordPropAlter(comp, oldCompProp, newCompProp, Inference::SPLITTING_COMPONENT);
  }
  if(env.options->showDefinitions() && newlyIntroduced) {
    env.out << "Definition: ";
    if(compName<0) {
      env.out << "~";
    }
    env.out << BDD::instance()->getPropositionalPredicateName(abs(compName))
      << " <=> (" << comp->nonPropToString() << ")" << endl;
  }
  return compName;
}

BDDNode* SWBSplitterWithBDDs::getNameProp(int name)
{
  CALL("SWBSplitterWithBDDs::getNameProp");
  ASS_NEQ(name,0);

  return BDD::instance()->getAtomic(abs(name), name>0);
}

}
