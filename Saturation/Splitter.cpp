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
#include "../Indexing/TermSharing.hpp"
#include "../Inferences/PropositionalToBDDISE.hpp"

#include "SaturationAlgorithm.hpp"

#include "Splitter.hpp"

namespace Saturation
{

using namespace Lib;
using namespace Kernel;
using namespace Inferences;

#define REPORT_SPLITS 0

void Splitter::init(SaturationAlgorithm* sa)
{
  CALL("Splitter::init");

  _sa=sa;
}

/**
 * Try to split clause @b cl into components, return true if successful
 *
 * When true is returned, the clause @b cl should not be kept in the
 * run of the saturation algorithm.
 *
 * The splitted components (or the clause replacement) are added to the
 * @b SaturationAlgorithm object through the @b addNewClause function,
 * also the function @b onParenthood is called with appropriate arguments.
 */
bool Splitter::doSplitting(Clause* cl)
{
  CALL("Splitter::doSplitting");

  BDD* bdd=BDD::instance();

  if(env.options->splitting()==Options::RA_INPUT_ONLY && !cl->isInput()) {
    return false;
  }

  int clen=cl->length();
  ASS_G(clen,0);

  if(clen<=1) {
    return false;
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
    return false;
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
    ASS(!colorComponent || masterComp==0);

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
	newMasterProp=bdd->disjunction(newMasterProp, getNameProp(compName));
#if REPORT_SPLITS
	cout<<compName<<": "<<(*comp)<<endl;
#endif
	if(bdd->isTrue(newMasterProp)) {
	  //the propositional part of the master component is true only
	  //due to already named components, so there's no point in adding
	  //any clause
	  return true;
	}
	masterPremises.push(comp);
	srec->namedComps.push(make_pair(compName, comp));
      }
    }
    else {
      if(colorComponent || (coloredMaster==-1 && !masterComp && compNew) ) {
	ASS_EQ(masterComp, 0);
	masterComp=comp;
      } else {
	unnamedComponentStack.push(comp);
      }
    }
    ASS(!colorComponent || masterComp!=0);
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

    newMasterProp=bdd->disjunction(newMasterProp, getNameProp(compName));

    if(bdd->isTrue(newMasterProp)) {
      delete srec;
      return true;
    }

    masterPremises.push(comp);
    srec->namedComps.push(make_pair(compName, comp));

#if REPORT_SPLITS
    cout<<'n'<<compName<<": "<<(*comp)<<endl;
#endif
  }

  InferenceStore::ClauseSpec splittedMCompCS=
    InferenceStore::getClauseSpec(masterComp, newMasterProp);

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

#if REPORT_SPLITS
  cout<<"^^^^^^^^^^^^\n";
#endif

  return true;
}

bool Splitter::canSplitOut(Literal* lit)
{
  return lit->color()==COLOR_TRANSPARENT &&
    (!env.options->showSymbolElimination() || lit->skip()) &&
    !env.signature->getPredicate(lit->functor())->cfName();
}

/**
 * Return component of @b cl that contains literals in array @b lits
 * (that has length @b compLen). If the component has a name,
 * assign it to @b name, otherwise assigh 0 to @b name.
 * Assign @b true to @b newComponent iff the component was
 * newly added to the component index.
 */
Clause* Splitter::getComponent(Clause* cl, Literal** lits, unsigned compLen, int& name, bool& newComponent)
{
  CALL("Splitter::getComponent");

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
    comp->setProp(BDD::instance()->getTrue());
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
int Splitter::nameComponent(Clause* comp)
{
  CALL("Splitter::nameComponent");

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
      _groundNames.insert(lit, compName);
    }
  }
  else {
    compName=BDD::instance()->getNewVar();
  }

  *pname=compName;
  BDDNode* oldCompProp=comp->prop();
  BDDNode* nameProp=BDD::instance()->getAtomic(abs(compName), compName<0);
  BDDNode* newCompProp=BDD::instance()->conjunction(oldCompProp, nameProp);
  if(newCompProp!=oldCompProp) {
    comp->setProp(newCompProp);
    InferenceStore::instance()->recordPropAlter(comp, oldCompProp, newCompProp, Inference::CLAUSE_NAMING);
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

BDDNode* Splitter::getNameProp(int name)
{
  CALL("Splitter::getNameProp");
  ASS_NEQ(name,0);

  return BDD::instance()->getAtomic(abs(name), name>0);
}


}
