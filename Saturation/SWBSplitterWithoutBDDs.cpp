/**
 * @file SWBSplitterWithoutBDDs.cpp
 * Implements class SWBSplitterWithoutBDDs.
 */

#include "Lib/Environment.hpp"
#include "Lib/List.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Indexing/TermSharing.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "SaturationAlgorithm.hpp"

#include "SWBSplitterWithoutBDDs.hpp"

namespace Saturation
{

using namespace Lib;
using namespace Kernel;

void SWBSplitterWithoutBDDs::buildAndInsertComponents(Clause* cl, const CompRec* comps, unsigned compCnt, bool firstIsMaster)
{
  CALL("SWBSplitterWithoutBDDs::buildAndInsertComponents");

#if REPORT_SPLITS
  cout<<"####SWBSplitterWithoutBDDs####\n";
  cout<<(*cl)<<endl;
  cout<<"vvv Into vvv\n";
#endif

  const CompRec& master=comps[0];

  static Stack<int> names;
  names.reset();

  UnitList* premises=0;

  for(unsigned i=1;i<compCnt;i++) {
    CompNameRec cnr=getNamedComponent(cl, comps[i]);
    names.push(cnr.name);
    UnitList::push(cnr.namingClause, premises);
  }
  UnitList::push(cl, premises);

  unsigned resLen=master.size()+names.size();

  Inference* inf=new InferenceMany(Inference::SPLITTING, premises);
  Unit::InputType inpType = cl->inputType();
  Clause* res = new(resLen) Clause(resLen, inpType, inf);
  for(unsigned i=0;i<master.size();i++) {
    (*res)[i]=master[i];
  }
  unsigned ri=master.size();
  while(names.isNonEmpty()) {
    (*res)[ri++]=getNameLiteral(names.pop(), true);
  }
  ASS_EQ(ri, resLen);

  res->setAge(cl->age());
  res->initProp(cl->prop());
  InferenceStore::instance()->recordNonPropInference(res);

  _sa->addNewClause(res);
  _sa->onClauseReduction(cl, res, 0);

#if REPORT_SPLITS
  cout<<(*res)<<endl;
  cout<<"^^^^^^^^^^^^\n";
#endif

}

/**
 * Name the component @b cr and return the @b CompNameRec
 * describing the naming
 *
 * If necessary, the naming clause is inserted into the
 * saturation algorithm.
 */
SWBSplitterWithoutBDDs::CompNameRec SWBSplitterWithoutBDDs::getNamedComponent(Clause* cl, const CompRec& cr)
{
  CALL("SWBSplitterWithoutBDDs::getNamedComponent");

  CompNameRec res(0,0);

  if(cr.size()==1 && cr[0]->ground()) {
    Literal* lit=cr[0];
    if(_groundNames.find(lit, res)) {
      return res;
    }
    if(_groundNames.find(Literal::complementaryLiteral(lit), res)) {
      int name=-res.name;
      res=createNamedComponent(cl, cr, name);
    }
  }

  if(res.isEmpty()) {
    res=createNamedComponent(cl, cr);
  }

  if(cr.size()==1 && cr[0]->ground()) {
    res.namingClause->incRefCnt();
    ALWAYS(_groundNames.insert(cr[0], res));
  }

  return res;
}

/**
 * Create a clause that names the component @b cr coming from the clause @b cr
 * using the name @b knownName. If @b knownName==0, a new name will ne used.
 *
 * The created clause is inserted into the saturation algorithm.
 */
SWBSplitterWithoutBDDs::CompNameRec SWBSplitterWithoutBDDs::createNamedComponent(Clause* cl, const CompRec& cr, int knownName)
{
  CALL("SWBSplitterWithoutBDDs::createNamedComponent");

  int name=knownName;
  if(!name) {
    name=getNewName();
  }

  unsigned resLen=cr.size()+1;

  Inference* inf=new Inference(Inference::SPLITTING_COMPONENT);
  Unit::InputType inpType = cl->inputType();
  Clause* res = new(resLen) Clause(resLen, inpType, inf);
  for(unsigned i=0;i<cr.size();i++) {
    (*res)[i]=cr[i];
  }

  Literal* nameLit=getNameLiteral(name, false);
  (*res)[cr.size()]=nameLit;

  res->setAge(cl->age());
  res->initProp(BDD::instance()->getFalse());
  InferenceStore::instance()->recordNonPropInference(res);

  InferenceStore::instance()->recordSplittingNameLiteral(UnitSpec(res), nameLit);


  _sa->addNewClause(res);
  _sa->onParenthood(res, cl);

#if REPORT_SPLITS
    cout<<'n'<<name<<": "<<(*res)<<endl;
#endif
  return CompNameRec(name, res);
}

/**
 * Return a new name for a component
 *
 * The returned name is an index of a new propositional
 * predicate symbol.
 */
int SWBSplitterWithoutBDDs::getNewName()
{
  CALL("SWBSplitterWithoutBDDs::getNewName");

  unsigned res=env.signature->addNamePredicate(0);
  env.signature->getPredicate(res)->markSWBName();

  env.statistics->splittingNamesIntroduced++;

  return res;
}

/**
 * Return naming literal for name @b name. If @b forMaster is true,
 * the literal to be used in the master component is returned,
 * otherwise it is a literal to be used in the clause that names
 * the component.
 */
Literal* SWBSplitterWithoutBDDs::getNameLiteral(int name, bool forMaster)
{
  CALL("SWBSplitterWithoutBDDs::getNameLiteral");
  ASS_NEQ(name, 0);

  bool positive=forMaster^(name>0);
  unsigned num=abs(name);

  return Literal::create(num, 0, positive, false, 0);
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
