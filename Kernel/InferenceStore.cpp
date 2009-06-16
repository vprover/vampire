/**
 * @file InferenceStore.cpp
 * Implements class InferenceStore.
 */

#include "../Lib/Allocator.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Stack.hpp"
#include "../Kernel/BDD.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/Formula.hpp"
#include "../Kernel/FormulaUnit.hpp"
#include "../Kernel/Inference.hpp"

#include "InferenceStore.hpp"

namespace Kernel
{

using namespace std;
using namespace Lib;

struct InferenceStore::FullInference
{
  FullInference(unsigned premCnt) : csId(0), premCnt(premCnt) { ASS_L(premCnt, 0xFFFF); }

  void* operator new(size_t,unsigned premCnt)
  {
    size_t size=sizeof(FullInference)+premCnt*sizeof(ClauseSpec);
    size-=sizeof(ClauseSpec);

    return ALLOC_KNOWN(size,"InferenceStore::FullInference");
  }

  size_t occupiedBytes()
  {
    size_t size=sizeof(FullInference)+premCnt*sizeof(ClauseSpec);
    size-=sizeof(ClauseSpec);
    return size;
  }

  int csId;
  unsigned premCnt : 16;
  Inference::Rule rule : 16;
  ClauseSpec premises[1];
};

InferenceStore::InferenceStore()
: _bdd(BDD::instance())
{
}


InferenceStore::ClauseSpec InferenceStore::getClauseSpec(Clause* cl)
{
  return ClauseSpec(cl, cl->prop());
}
InferenceStore::ClauseSpec InferenceStore::getClauseSpec(Clause* cl, BDDNode* prop)
{
  return ClauseSpec(cl, prop);
}

string InferenceStore::getClauseIdStr(ClauseSpec cs)
{
  string res=Int::toString(cs.first->number());
  FullInference* finf;
  if(_data.find(cs,finf)) {
    if(!finf->csId) {
      finf->csId=_nextClIds.insert(cs.first);
    }
    return res+"_"+Int::toString(finf->csId);
  } else {
    //only clause constant prop. part can miss their Kernel-inference.
    if(_bdd->isTrue(cs.second)) {
      return res+"_T";
    } else {
      ASS(_bdd->isFalse(cs.second));
      return res;
    }
  }
}

void InferenceStore::recordNonPropInference(Clause* cl)
{
  CALL("InferenceStore::recordNonPropInference/1");

  Inference* cinf=cl->inference();
  Inference::Iterator it = cinf->iterator();
  bool nonTrivialProp=false;
  while (cinf->hasNext(it)) {
    Clause* prem=static_cast<Clause*>(cinf->next(it));
    ASS(prem->isClause());
    if(!_bdd->isFalse(prem->prop())) {
      nonTrivialProp=true;
      break;
    }
  }

  if(nonTrivialProp) {
    recordNonPropInference(cl, cl->inference());
  }


}

void InferenceStore::recordNonPropInference(Clause* cl, Inference* cinf)
{
  CALL("InferenceStore::recordNonPropInference/2");
  ASS(!_bdd->isTrue(cl->prop()));

  static Stack<Clause*> prems(8);
  prems.reset();

  Inference::Iterator it = cinf->iterator();
  while (cinf->hasNext(it)) {
    Clause* prem=static_cast<Clause*>(cinf->next(it));
    ASS(prem->isClause());
    prems.push(prem);
  }

  unsigned premCnt=prems.size();
  FullInference* finf=new (premCnt) FullInference(premCnt);
  for(unsigned i=0;i<premCnt;i++) {
    finf->premises[i]=getClauseSpec(prems[i]);
  }
  finf->rule=cinf->rule();
  _data.insert(getClauseSpec(cl), finf);
}

void InferenceStore::recordPropReduce(Clause* cl, BDDNode* oldProp, BDDNode* newProp)
{
  if(_bdd->isTrue(cl->prop())) {
    return;
  }
  recordPropAlter(cl, oldProp, newProp, Inference::PROP_REDUCE);
}

void InferenceStore::recordPropAlter(Clause* cl, BDDNode* oldProp, BDDNode* newProp,
	Inference::Rule rule)
{
  ASS(!_bdd->isTrue(newProp));

  FullInference* finf=new (1) FullInference(1);
  finf->premises[0]=getClauseSpec(cl, oldProp);

  finf->rule=rule;
  _data.insert(getClauseSpec(cl, newProp), finf);
}

void InferenceStore::recordMerge(Clause* cl, BDDNode* oldClProp, Clause* addedCl, BDDNode* resultProp)
{
  ASS(!_bdd->isTrue(resultProp));

  FullInference* finf=0;
  finf=new (2) FullInference(2);
  finf->premises[0]=getClauseSpec(cl, oldClProp);
  finf->premises[1]=getClauseSpec(addedCl);
  finf->rule=Inference::COMMON_NONPROP_MERGE;
  _data.insert(getClauseSpec(cl, resultProp), finf);
}

void InferenceStore::recordSplitting(Clause* master, BDDNode* oldMasterProp, BDDNode* newMasterProp,
	  unsigned premCnt, Clause** prems)
{
  ASS(!_bdd->isTrue(newMasterProp));

  FullInference* finf=new (premCnt+1) FullInference(premCnt+1);
  for(unsigned i=0;i<premCnt;i++) {
    finf->premises[i]=getClauseSpec(prems[i]);
  }
  finf->premises[premCnt]=getClauseSpec(master, oldMasterProp);

  finf->rule=Inference::SPLITTING;
  _data.insert(getClauseSpec(master, newMasterProp), finf);
}


struct InferenceStore::ProofPrinter
{
  ProofPrinter(Unit* refutation, ostream& out, InferenceStore* is)
  : is(is), out(out), bdd(BDD::instance()), dummyTautIntroduction(0)
  {
    dummyTautIntroduction.rule=Inference::TAUTOLOGY_INTRODUCTION;

    if( refutation->isClause() && static_cast<Clause*>(refutation)->prop() ) {
      Clause* refCl=static_cast<Clause*>(refutation);
      ASS( bdd->isFalse(refCl->prop()) );
      ClauseSpec cs=getClauseSpec(refCl);
      outKernel.push(cs);
      handledKernel.insert(cs);
    } else {
      outShell.push(refutation);
      handledShell.insert(refutation);
    }
  }

  virtual ~ProofPrinter() {}

  virtual void printProofStepHead(ClauseSpec cs, FullInference* finf)
  {
    Clause* cl=cs.first;

    out << is->getClauseIdStr(cs) << ". "
	<< cl->nonPropToString()
	<<" | "<<bdd->toString(cs.second)
	<<" ("<<cl->age()<<':'<<cl->weight()<<") ";

    out <<"["<<Inference::ruleName(finf->rule);
  }

  virtual void printProofStepPremise(ClauseSpec cs, bool first)
  {
    out << (first ? ' ' : ',');
    out << is->getClauseIdStr(cs);
  }

  virtual void printProofStepHead(Unit* unit)
  {
    out << unit->number() << ". ";
    if(unit->isClause()) {
      Clause* cl=static_cast<Clause*>(unit);
      out << cl->nonPropToString() << " ("<<cl->age()<<':'<<cl->weight()<<")";
    } else {
      FormulaUnit* fu=static_cast<FormulaUnit*>(unit);
      out << fu->formula()->toString();
    }
    out << " [" << unit->inference()->name();
  }

  virtual void printProofStepPremise(Unit* unit, bool first)
  {
    out << (first ? ' ' : ',');
    out << unit->number();
  }

  virtual void printProofStepTail()
  {
    out << "]\n";
  }

  virtual bool hideProofStep(Inference::Rule rule)
  {
    return false;
  }

  void print()
  {
    while(outKernel.isNonEmpty()) {
      ClauseSpec cs=outKernel.pop();
      FullInference* finf;
      if(bdd->isTrue(cs.second)) {
	//a tautology does not need any proof
	ASS(!is->_data.find(cs));
	if(!hideProofStep(Inference::TAUTOLOGY_INTRODUCTION)) {
	  printProofStepHead(cs, &dummyTautIntroduction);
	  printProofStepTail();
	}
      } else if(is->_data.find(cs, finf)) {
	bool hideStep=hideProofStep(finf->rule);

	if(!hideStep) {
	  printProofStepHead(cs, finf);
	}

	for(unsigned i=0;i<finf->premCnt;i++) {
	  ClauseSpec prem=finf->premises[i];
	  Clause* premCl=prem.first;
	  if(!hideStep) {
	    printProofStepPremise(prem, i==0);
	  }
	  ASS(premCl->prop());
	  if(!handledKernel.contains(prem)) {
	    handledKernel.insert(prem);
	    outKernel.push(prem);
	  }
	}
	if(!hideStep) {
	  printProofStepTail();
	}
      } else {
	Clause* cl=cs.first;
	Inference* inf = cl->inference();
	bool hideStep=hideProofStep(inf->rule());

	if(!hideStep) {
	  printProofStepHead(cl);
	}
	Inference::Iterator it = inf->iterator();
	bool first=true;
	while (inf->hasNext(it)) {
	  Unit* prem=inf->next(it);
	  if(!hideStep) {
	    printProofStepPremise(prem, first);
	  }
	  first=false;
	  if(prem->isClause() && static_cast<Clause*>(prem)->prop()) {
	    ClauseSpec premCS=getClauseSpec(static_cast<Clause*>(prem), bdd->getFalse());
	    if(!handledKernel.contains(premCS)) {
	      handledKernel.insert(premCS);
	      outKernel.push(premCS);
	    }
	  } else {
	    if(!handledShell.contains(prem)) {
	      handledShell.insert(prem);
	      outShell.push(prem);
	    }
	  }
	}
	if(!hideStep) {
	  printProofStepTail();
	}
      }
    }

    while(outShell.isNonEmpty()) {
      Unit* unit=outShell.pop();
      Inference* inf = unit->inference();
      bool hideStep=hideProofStep(inf->rule());

      if(!hideStep) {
	printProofStepHead(unit);
      }
      Inference::Iterator it = inf->iterator();
      bool first=true;
      while (inf->hasNext(it)) {
	Unit* prem=inf->next(it);
	if(!hideStep) {
	  printProofStepPremise(prem, first);
	}
	first=false;
	if(!handledShell.contains(prem)) {
	  handledShell.insert(prem);
	  outShell.push(prem);
	}
      }
      if(!hideStep) {
	printProofStepTail();
      }
    }
  }

  /** Clauses that have propositional part assigned are put here
   * to be output as an inference step */
  Stack<ClauseSpec> outKernel;
  Set<ClauseSpec> handledKernel;

  Stack<Unit*> outShell;
  Set<Unit*> handledShell;

  InferenceStore* is;
  ostream& out;
  BDD* bdd;

  FullInference dummyTautIntroduction;
};

struct InferenceStore::TPTPProofCheckPrinter
: InferenceStore::ProofPrinter
{
  TPTPProofCheckPrinter(Unit* refutation, ostream& out, InferenceStore* is)
  : ProofPrinter(refutation, out, is) {}

  void printProofStepHead(ClauseSpec cs, FullInference* finf)
  {
    Clause* cl=cs.first;
    out << "fof(r"<<is->getClauseIdStr(cs)
    	<< ",conjecture, "
    	<< cl->nonPropToString()<<" | "<<bdd->toTPTPString(cs.second)
    	<< " ). %"<<Inference::ruleName(finf->rule)<<"\n";
  }

  void printProofStepPremise(ClauseSpec cs, bool first)
  {
    Clause* cl=cs.first;
    out << "fof(pr"<<is->getClauseIdStr(cs)
	<< ",axiom, "
	<< cl->nonPropToString()<<" | "<<bdd->toTPTPString(cs.second)
    	<< " ).\n";
  }

  void printProofStepHead(Unit* unit)
  {
    out << "fof(r"<<unit->number()<<",conjecture, ";
    if(unit->isClause()) {
      Clause* cl=static_cast<Clause*>(unit);
      out << cl->nonPropToString();
    } else {
      FormulaUnit* fu=static_cast<FormulaUnit*>(unit);
      out << fu->formula()->toString();
    }
    out << " ). %"<<unit->inference()->name()<<"\n";
  }

  void printProofStepPremise(Unit* unit, bool first)
  {
    out << "fof(pr"<<unit->number()<<",axiom, ";
    if(unit->isClause()) {
      Clause* cl=static_cast<Clause*>(unit);
      out << cl->nonPropToString();
    } else {
      FormulaUnit* fu=static_cast<FormulaUnit*>(unit);
      out << fu->formula()->toString();
    }
    out << " ).\n";
  }

  void printProofStepTail()
  {
    out << "%#\n";
  }

  bool hideProofStep(Inference::Rule rule)
  {
    switch(rule) {
    case Inference::INPUT:
    case Inference::NEGATED_CONJECTURE:
    case Inference::CLAUSE_NAMING:
    case Inference::SPLITTING_COMPONENT:
    case Inference::INEQUALITY_SPLITTING_NAME_INTRODUCTION:
    case Inference::INEQUALITY_SPLITTING:
      return true;
    default:
      return false;
    }
  }
};

void InferenceStore::outputProof(ostream& out, Unit* refutation)
{
  CALL("InferenceStore::outputProof");

  ProofPrinter pp(refutation, out, this);
//  TPTPProofCheckPrinter pp(refutation, out, this);
//  out << "%#\n";
  pp.print();
}


InferenceStore* InferenceStore::instance()
{
  static InferenceStore* inst=0;
  if(!inst) {
    inst=new InferenceStore();
  }
  return inst;
}


}
