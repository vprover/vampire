/**
 * @file InferenceStore.cpp
 * Implements class InferenceStore.
 */

#include "../Lib/Allocator.hpp"
#include "../Lib/Stack.hpp"
#include "../Kernel/BDD.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/Formula.hpp"
#include "../Kernel/FormulaUnit.hpp"
#include "../Kernel/Inference.hpp"

#include "InferenceStore.hpp"

namespace Kernel
{

using namespace Lib;

struct InferenceStore::FullInference
{
  FullInference(unsigned premCnt) : csId(0), premCnt(premCnt) {}

  void* operator new(size_t,unsigned premCnt)
  {
    size_t size=sizeof(FullInference)+premCnt*sizeof(ClauseSpec);
    size-=sizeof(ClauseSpec*);

    return ALLOC_KNOWN(size,"InferenceStore::FullInference");
  }

  int csId;
  unsigned premCnt;
  Inference::Rule rule;
  ClauseSpec premises[1];
};

InferenceStore::ClauseSpec InferenceStore::getClauseSpec(Clause* cl)
{
  return ClauseSpec(cl, cl->prop());
}
InferenceStore::ClauseSpec InferenceStore::getClauseSpec(Clause* cl, BDDNode* prop)
{
  return ClauseSpec(cl, prop);
}

int InferenceStore::getClauseSpecId(ClauseSpec cs)
{
  FullInference* finf;
  if(_data.find(cs,finf)) {
    if(!finf->csId) {
      finf->csId=_nextClIds.insert(cs.first);
    }
    return finf->csId;
  } else {
    //only clause without prop. part can miss their Kernel-inference.
    ASS(BDD::instance()->isFalse(cs.second));
    return 0;
  }
}

void InferenceStore::recordNonPropInference(Clause* cl)
{
  CALL("InferenceStore::recordNonPropInference");

  static Stack<Clause*> prems(8);
  prems.reset();

  Inference* cinf = cl->inference();
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
  recordPropAlter(cl, oldProp, newProp, Inference::PROP_REDUCE);
}

void InferenceStore::recordPropAlter(Clause* cl, BDDNode* oldProp, BDDNode* newProp,
	Inference::Rule rule)
{
  FullInference* finf=new (1) FullInference(1);
  finf->premises[0]=getClauseSpec(cl, oldProp);

  finf->rule=rule;
  _data.insert(getClauseSpec(cl, newProp), finf);
}

void InferenceStore::recordMerge(Clause* cl, BDDNode* oldClProp, Clause* addedCl, BDDNode* resultProp)
{
  FullInference* finf=new (2) FullInference(2);
  finf->premises[0]=getClauseSpec(cl, oldClProp);
  finf->premises[1]=getClauseSpec(addedCl);

  finf->rule=Inference::COMMON_NONPROP_MERGE;
  _data.insert(getClauseSpec(cl, resultProp), finf);
}

void InferenceStore::recordSplitting(Clause* master, BDDNode* oldMasterProp, BDDNode* newMasterProp,
	  unsigned premCnt, Clause** prems)
{
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
  : is(is), out(out), bdd(BDD::instance())
  {
    if( refutation->isClause() && is->_data.find(getClauseSpec(static_cast<Clause*>(refutation))) ) {
      ClauseSpec cs=getClauseSpec(static_cast<Clause*>(refutation));
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
    int csId=is->getClauseSpecId(cs);
    ASS(csId);
    out << cl->number()<<"_"<<csId<<". "
	<< cl->nonPropToString()
	<<" | "<<bdd->toString(cs.second)
	<<" ("<<cl->age()<<':'<<cl->weight()<<") ";

    out <<"["<<Inference::ruleName(finf->rule);
  }

  virtual void printProofStepPremise(ClauseSpec cs, bool first)
  {
    Clause* cl=cs.first;
    int csId=is->getClauseSpecId(cs);
    out << (first ? ' ' : ',');
    out << cl->number();
    if(csId) {
      out << "_"<<csId;
    }
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
      FullInference* finf=is->_data.get(cs);
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
	int csId=is->getClauseSpecId(prem);
	if(csId) {
	  if(!handledKernel.contains(prem)) {
	    handledKernel.insert(prem);
	    outKernel.push(prem);
	  }
	} else {
	  if(!handledShell.contains(premCl)) {
	    handledShell.insert(premCl);
	    outShell.push(premCl);
	  }
	}
      }
      if(!hideStep) {
	printProofStepTail();
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

  Stack<ClauseSpec> outKernel;
  Stack<Unit*> outShell;
  Set<ClauseSpec> handledKernel;
  Set<Unit*> handledShell;

  InferenceStore* is;
  ostream& out;
  BDD* bdd;
};

struct InferenceStore::TPTPProofCheckPrinter
: InferenceStore::ProofPrinter
{
  TPTPProofCheckPrinter(Unit* refutation, ostream& out, InferenceStore* is)
  : ProofPrinter(refutation, out, is) {}

  void printProofStepHead(ClauseSpec cs, FullInference* finf)
  {
    Clause* cl=cs.first;
    int csId=is->getClauseSpecId(cs);
    out << "fof(r"<<cl->number()<<"_"<<csId<<",conjecture, ";
    out << cl->nonPropToString()<<" | "<<bdd->toTPTPString(cs.second);
    out << " ). %"<<Inference::ruleName(finf->rule)<<"\n";
  }

  void printProofStepPremise(ClauseSpec cs, bool first)
  {
    Clause* cl=cs.first;
    int csId=is->getClauseSpecId(cs);
    out << "fof(pr"<<cl->number();
    if(csId) {
      out << "_"<<csId;
    }
    out << ",axiom, ";
    out << cl->nonPropToString()<<" | "<<bdd->toTPTPString(cs.second);
    out << " ).\n";
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
