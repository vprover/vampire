/**
 * @file SWBSplitterWithoutBDDs.cpp
 * Implements class SWBSplitterWithoutBDDs.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/List.hpp"
#include "../Lib/Stack.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/InferenceStore.hpp"
#include "../Kernel/Signature.hpp"
#include "../Kernel/Term.hpp"

#include "../Indexing/TermSharing.hpp"

#include "../Shell/Options.hpp"
#include "../Shell/Statistics.hpp"

#include "SaturationAlgorithm.hpp"

#include "SWBSplitterWithoutBDDs.hpp"

namespace Saturation
{

using namespace Lib;
using namespace Kernel;

void SWBSplitterWithoutBDDs::buildAndInsertComponents(Clause* cl, CompRec* comps, unsigned compCnt, bool firstIsMaster)
{
  CALL("SWBSplitterWithoutBDDs::buildAndInsertComponents");

#if REPORT_SPLITS
  cout<<"####SWBSplitterWithoutBDDs####\n";
  cout<<(*cl)<<endl;
  cout<<"vvv Into vvv\n";
#endif

  CompRec master=comps[0];

  static Stack<int> names;
  names.reset();

  UnitList* premises=0;

  for(unsigned i=1;i<compCnt;i++) {
    CompNameRec cnr=getNamedComponent(cl, comps[i]);
    names.push(cnr.name);
    UnitList::push(cnr.namingClause, premises);
  }
  UnitList::push(cl, premises);

  unsigned resLen=master.len+names.size();

  Inference* inf=new InferenceMany(Inference::SPLITTING, premises);
  Unit::InputType inpType = cl->inputType();
  Clause* res = new(resLen) Clause(resLen, inpType, inf);
  for(unsigned i=0;i<master.len;i++) {
    (*res)[i]=master.lits[i];
  }
  unsigned ri=master.len;
  while(names.isNonEmpty()) {
    (*res)[ri++]=getNameLiteral(names.pop(), true);
  }
  ASS_EQ(ri, resLen);

  res->setAge(cl->age());
  res->setProp(cl->prop());
  InferenceStore::instance()->recordNonPropInference(res);

  _sa->addNewClause(res);
  _sa->onClauseReduction(cl, res, 0);

#if REPORT_SPLITS
  cout<<(*res)<<endl;
  cout<<"^^^^^^^^^^^^\n";
#endif

}

SWBSplitterWithoutBDDs::CompNameRec SWBSplitterWithoutBDDs::getNamedComponent(Clause* cl, CompRec cr)
{
  CALL("SWBSplitterWithoutBDDs::getNamedComponent");

  CompNameRec res(0,0);

  if(cr.len==1 && cr.lits[0]->ground()) {
    Literal* lit=cr.lits[0];
    if(_groundNames.find(lit, res)) {
      return res;
    }
    if(_groundNames.find(Literal::oppositeLiteral(lit), res)) {
      int name=-res.name;
      res=createNamedComponent(cl, cr, name);
    }
  }

  if(res.isEmpty()) {
    res=createNamedComponent(cl, cr);
  }

  if(cr.len==1 && cr.lits[0]->ground()) {
    ALWAYS(_groundNames.insert(cr.lits[0], res));
  }

  return res;
}

/**
 * Create a clause that names the component @b cr coming from the clause @b cr
 * using the name @b knownName. If @b knownName==0, a new name will ne used.
 */
SWBSplitterWithoutBDDs::CompNameRec SWBSplitterWithoutBDDs::createNamedComponent(Clause* cl, CompRec cr, int knownName)
{
  CALL("SWBSplitterWithoutBDDs::createNamedComponent");

  int name=knownName;
  if(!name) {
    name=getNewName();
  }

  unsigned resLen=cr.len+1;

  Inference* inf=new Inference(Inference::SPLITTING_COMPONENT);
  Unit::InputType inpType = cl->inputType();
  Clause* res = new(resLen) Clause(resLen, inpType, inf);
  for(unsigned i=0;i<cr.len;i++) {
    (*res)[i]=cr.lits[i];
  }
  (*res)[cr.len]=getNameLiteral(name, false);

  res->setAge(cl->age());
  res->setProp(BDD::instance()->getFalse());
  InferenceStore::instance()->recordNonPropInference(res);

  _sa->addNewClause(res);
  _sa->onParenthood(res, cl);

#if REPORT_SPLITS
    cout<<'n'<<name<<": "<<(*res)<<endl;
#endif
  return CompNameRec(name, res);
}

int SWBSplitterWithoutBDDs::getNewName()
{
  CALL("SWBSplitterWithoutBDDs::getNewName");

  unsigned res=env.signature->addNamePredicate(0);
  env.signature->getPredicate(res)->markSWBName();

  env.statistics->splittingNamesIntroduced++;

  return res;
}

Literal* SWBSplitterWithoutBDDs::getNameLiteral(int name, bool forMaster)
{
  CALL("SWBSplitterWithoutBDDs::getNameLiteral");
  ASS_NEQ(name, 0);

  bool positive=forMaster^(name>0);
  unsigned num=abs(name);

  return Literal::create(num, 0, positive, false, 0);
}

bool SWBSplitterWithoutBDDs::handleNoSplit(Clause* cl)
{
  CALL("SWBSplitterWithoutBDDs::handleNoSplit");

  return false;
}

bool SWBSplitterWithoutBDDs::canStandAlone(Literal* lit)
{
  return SWBSplitter::canStandAlone(lit) && lit->arity()!=0;
}

bool SWBSplitterWithoutBDDs::standAloneObligations()
{
  return true;
}

}
